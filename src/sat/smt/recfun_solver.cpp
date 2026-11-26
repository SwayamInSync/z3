/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    recfun_solver.cpp

Abstract:

    Recursive function solver plugin

Author:

    Nikolaj Bjorner (nbjorner) 2021-02-09

--*/

#include "ast/rewriter/var_subst.h"
#include "sat/smt/recfun_solver.h"
#include "sat/smt/euf_solver.h"


#define TRACEFN(x) TRACE(recfun, tout << x << '\n';)


namespace recfun {


    solver::solver(euf::solver& ctx):
        th_euf_solver(ctx, symbol("recfun"), ctx.get_manager().mk_family_id("recfun")),
        m_plugin(*reinterpret_cast<recfun::decl::plugin*>(m.get_plugin(ctx.get_manager().mk_family_id("recfun")))),
        m_util(m_plugin.u()), 
        m_disabled_guards(m),
        m_enabled_guards(m),
        m_assumptions(m),
        m_owed(m),
        m_certain(m),
        m_preds(m) {
    }    

    solver::~solver() {
        reset();
    }

    void solver::reset() {
        m_stats.reset();
        m_disabled_guards.reset();
        m_disabled.reset();
        m_enabled_guards.reset();
        m_enabled.reset();
        m_assumptions.reset();
        m_guard2assumption.reset();
        m_assumption2guard.reset();
        m_assumed.reset();
        m_owed.reset();
        m_certain.reset();
        m_bodied.reset();
        m_retired.reset();
        m_limited = nullptr;
        m_propagation_queue.reset();
    }

    expr_ref solver::apply_args(vars const & vars, expr_ref_vector const & args, expr * e) {
        SASSERT(is_standard_order(vars));
        var_subst subst(m, true);
        expr_ref new_body = subst(e, args);
        ctx.get_rewriter()(new_body);
        return new_body;
    }

    /**
     * For functions f(args) that are given as macros f(vs) = rhs
     * 
     * 1. substitute `e.args` for `vs` into the macro rhs
     * 2. add unit clause `f(args) = rhs`
     */
    void solver::assert_macro_axiom(case_expansion & e) {
        m_stats.m_macro_expansions++;
        TRACEFN("case expansion " << e);
        SASSERT(e.m_def->is_fun_macro());
        auto & vars = e.m_def->get_vars();
        app_ref lhs = e.m_lhs;
        expr_ref rhs = apply_args(vars, e.m_args, e.m_def->get_rhs());
        unsigned generation = std::max(ctx.get_max_generation(lhs), ctx.get_max_generation(rhs));
        euf::solver::scoped_generation _sgen(ctx, generation + 1);
        auto eq = eq_internalize(lhs, rhs);
        add_unit(eq);        
    }

    /**
     * Add case axioms for every case expansion path.
     *
     * assert `p(args) <=> And(guards)` (with CNF on the fly)
     *
     * also body-expand paths that do not depend on any defined fun
     */
    void solver::assert_case_axioms(case_expansion & e) {
        if (e.m_def->is_fun_macro()) {
            assert_macro_axiom(e);
            return;
        }

        ++m_stats.m_case_expansions;
        TRACEFN("assert_case_axioms " << e
                << " with " << e.m_def->get_cases().size() << " cases");
        SASSERT(e.m_def->is_fun_defined());
        // add case-axioms for all case-paths
        // assert this was not defined before.
        sat::literal_vector preds;
        auto & vars = e.m_def->get_vars();
            
        for (case_def const & c : e.m_def->get_cases()) {
            // applied predicate to `args`
            app_ref pred_applied = c.apply_case_predicate(e.m_args);
            SASSERT(u().owns_app(pred_applied));
            preds.push_back(mk_literal(pred_applied));
            expr_ref_vector guards(m);
            for (auto & g : c.get_guards()) 
                guards.push_back(apply_args(vars, e.m_args, g));
            if (c.is_immediate()) {
                body_expansion be(pred_applied, c, e.m_args);
                assert_body_axiom(be);            
            }
            else if (!is_enabled_guard(pred_applied)) 
                disable_guard(pred_applied);
            // a disabled guard keeps its definition, see theory_recfun.
            assert_guard(pred_applied, guards);
        }
        add_clause(preds);
    }
    
    void solver::assert_guard(expr* pred_applied, expr_ref_vector const& guards) {
        sat::literal_vector lguards;
        for (expr* ga : guards) 
            lguards.push_back(mk_literal(ga));
        add_equiv_and(mk_literal(pred_applied), lguards);
    }

    /**
     * A clause of the depth limit holds under the assumptions of a round. It
     * is not a theorem of the definitions, so it is added as an input clause,
     * which a proof checker takes as given.
     */
    void solver::block_core(expr_ref_vector const& core) {
        sat::literal_vector clause;
        for (expr* e : core)
            clause.push_back(~mk_literal(e));
        ctx.add_root(clause.size(), clause.data());
        s().add_clause(clause.size(), clause.data(), sat::status::input());
    }

    bool solver::has_definition(expr* guard) const {
        return m_plugin.has_case_def(to_app(guard)->get_decl());
    }

    bool solver::holds(expr* e) {
        euf::enode* n = expr2enode(e);
        return n && n->bool_var() != sat::null_bool_var && s().value(n->bool_var()) == l_true;
    }

    expr_ref solver::limit_of(expr* guard) {
        if (m_assumed.contains(guard))
            return expr_ref(m_guard2assumption[guard], m);
        return expr_ref(round(), m);
    }

    /**
     * The guard appears at a depth below the current cutoff: it keeps its
     * definition but gets no body. The depth limit is lazy: the clauses
     * `limit & p => ~guard` take effect when check_last adds `round => limit`.
     * See theory_recfun::disable_guard.
     */
    void solver::disable_guard(expr* guard) {
        SASSERT(!is_enabled_guard(guard));
        if (!m_guard2assumption.contains(guard)) {
            app_ref assumption = m_util.mk_depth_limit_pred(m_assumptions.size() + 1);
            m_assumptions.push_back(assumption);
            m_guard2assumption.insert(guard, assumption);
            m_assumption2guard.insert(assumption, guard);
            m_disabled_guards.push_back(guard);
            m_disabled.insert(guard);
        }
        // a guard that appears while the limit is on is limited from the start.
        if (holds(limit()))
            m_limited = guard;
        expr_ref_vector core(m);
        core.push_back(limit());
        core.push_back(m_guard2assumption[guard]);
        core.push_back(guard);
        TRACEFN("add clause\n" << core);
        push_c(core);
        if (!m_assumed.contains(guard)) {
            core[1] = round();
            TRACEFN("add clause\n" << core);
            push_c(core);
        }
    }

    void solver::enable_guard(expr* guard) {
        SASSERT(is_disabled_guard(guard));
        m_enabled_guards.push_back(guard);
        m_enabled.insert(guard);
        m_disabled_guards.erase(guard);
        m_disabled.remove(guard);
        m_assumed.remove(guard);
    }

    /**
     * Queue the body of a guard, once for as long as the queue entry lives.
     */
    void solver::expand_body(expr* guard) {
        if (m_bodied.contains(guard) || !has_definition(guard))
            return;
        m_bodied.insert(guard);
        ctx.push(insert_obj_trail<expr>(m_bodied, guard));
        push_body_expand(guard);
    }

    /**
     * For a guarded definition guards => f(vars) = rhs
     * and occurrence f(args)
     *
     * substitute `args` for `vars` in guards, and rhs
     * add axiom guards[args/vars] => f(args) = rhs[args/vars]
     *
     */
    void solver::assert_body_axiom(body_expansion & e) {
        ++m_stats.m_body_expansions;
        recfun::def & d = *e.m_cdef->get_def();
        auto & vars = d.get_vars();
        auto & args = e.m_args;
        SASSERT(is_standard_order(vars));
        sat::literal_vector clause;
        for (auto & g : e.m_cdef->get_guards()) {
            expr_ref guard = apply_args(vars, args, g);
            if (m.is_false(guard))
                return;
            if (m.is_true(guard))
                continue;
            clause.push_back(~mk_literal(guard));
        }        
        expr_ref lhs(u().mk_fun_defined(d, args), m);
        expr_ref rhs = apply_args(vars, args, e.m_cdef->get_rhs());
        if (m.is_true(rhs))
            clause.push_back(mk_literal(lhs));
        else if (m.is_false(rhs))
            clause.push_back(~mk_literal(lhs));
        else
            clause.push_back(eq_internalize(lhs, rhs));
        add_clause(clause);
    }

    void solver::get_antecedents(sat::literal l, sat::ext_justification_idx idx, sat::literal_vector& r, bool probing) {
        UNREACHABLE();
    }

    void solver::asserted(sat::literal l) {
        expr* e = ctx.bool_var2expr(l.var());
        if (l.sign() || !e || !u().is_case_pred(e))
            return;
        // A disabled guard gets no body. The body is owed for as long as the
        // assignment lasts; add_assumptions pays it once the guard is enabled.
        if (is_disabled_guard(e)) {
            m_owed.push_back(e);
            ctx.push(push_back_vector<expr_ref_vector>(m_owed));
            return;
        }
        expand_body(e);
    }

    sat::check_result solver::check() {
        return sat::check_result::CR_DONE;
    }

    /**
     * The assignment is accepted by every theory solver. A disabled guard
     * that is true in it relies on an unfolding below the current cutoff.
     * See theory_recfun::final_check_last_eh.
     */
    sat::check_result solver::check_last() {
        bool unfolded = false;
        for (expr* g : m_disabled_guards) {
            if (!holds(g) || !has_definition(g))
                continue;
            expr_ref lim = limit_of(g);
            if (!holds(lim)) {
                if (!m_bodied.contains(g)) {
                    TRACEFN("unfold without a limit\n" << mk_pp(g, m));
                    expand_body(g);
                    unfolded = true;
                }
                continue;
            }
            TRACEFN("apply the depth limit\n" << mk_pp(g, m));
            // A disabled guard that is true without a decision is needed by
            // every assignment of the round, whatever the search guessed.
            for (expr* h : m_disabled_guards)
                if (holds(h) && has_definition(h) && s().lvl(expr2enode(h)->bool_var()) <= s().search_lvl() && !m_certain.contains(h))
                    m_certain.push_back(h);
            expr_ref_vector core(m);
            if (holds(round())) {
                core.push_back(round());
                core.push_back(m.mk_not(limit()));
                block_core(core);
                core.reset();
            }
            if (!s().inconsistent()) {
                core.push_back(lim);
                core.push_back(g);
                block_core(core);
            }
            return sat::check_result::CR_CONTINUE;
        }
        return unfolded ? sat::check_result::CR_CONTINUE : sat::check_result::CR_DONE;
    }

    std::ostream& solver::display(std::ostream& out) const {
        return out << "disabled guards:\n" << m_disabled_guards << "\n";
    }

    void solver::collect_statistics(statistics& st) const {
        st.update("recfun macro expansion", m_stats.m_macro_expansions);
        st.update("recfun case expansion", m_stats.m_case_expansions);
        st.update("recfun body expansion", m_stats.m_body_expansions);
    }

    euf::th_solver* solver::clone(euf::solver& ctx) {
        return alloc(solver, ctx);
    }

    bool solver::unit_propagate() {
        force_push();
        if (m_qhead == m_propagation_queue.size())
            return false;
        ctx.push(value_trail<unsigned>(m_qhead));
        // Yield to the context's resource checks before processing newly queued expansions.
        for (unsigned end = m_propagation_queue.size(); m_qhead < end && !s().inconsistent(); ++m_qhead) {
            auto& p = *m_propagation_queue[m_qhead];
            if (p.is_core()) 
                block_core(p.core());
            else if (p.is_case()) 
                assert_case_axioms(p.case_ex());
            else 
                assert_body_axiom(p.body());
        }
        return true;
    }

    void solver::push_prop(propagation_item* p) {
        m_propagation_queue.push_back(p);        
        ctx.push(push_back_vector<scoped_ptr_vector<propagation_item>>(m_propagation_queue));        
    }

    sat::literal solver::internalize(expr* e, bool sign, bool root) {
        force_push();
        SASSERT(m.is_bool(e));
        if (!visit_rec(m, e, sign, root)) {
            TRACE(array, tout << mk_pp(e, m) << "\n";);
            return sat::null_literal;
        }
        auto lit = expr2literal(e);
        if (sign)
            lit.neg();
        return lit;
    }

    void solver::internalize(expr* e) {
        force_push();
        visit_rec(m, e, false, false);
    }

    bool solver::visited(expr* e) {
        euf::enode* n = expr2enode(e);
        return n && n->is_attached_to(get_id());        
    }

    bool solver::visit(expr* e) {
        if (visited(e))
            return true;
        if (!is_app(e) || to_app(e)->get_family_id() != get_id()) {
            ctx.internalize(e);
            return true;
        }
        m_stack.push_back(sat::eframe(e));
        return false;        
    }

    bool solver::post_visit(expr* e, bool sign, bool root) {
        euf::enode* n = expr2enode(e);
        SASSERT(!n || !n->is_attached_to(get_id()));
        if (!n) 
            n = mk_enode(e, false);
        if (n->is_attached_to(get_id()))
            return true;
        euf::theory_var w = mk_var(n);
        ctx.attach_th_var(n, this, w);
        if (u().is_defined(e) && u().has_defs()) 
            push_case_expand(e);
        return true;
    }

    /**
     * Start a search: assume the round predicate and the predicate of every
     * disabled guard, and restore what the guards need in the current scope.
     */
    void solver::add_assumptions(sat::literal_set& assumptions) {
        if (!u().has_defs() && m_disabled_guards.empty())
            return;
        app_ref dlimit = round();
        TRACEFN("add_theory_assumption " << dlimit);
        sat::literal assumption = mk_literal(dlimit); 
        assumptions.insert(assumption);
        s().assign_scoped(assumption);
        m_assumed.reset();
        m_limited = nullptr;
        m_certain.reset();
        for (expr* g : m_disabled_guards) {
            assumption = mk_literal(m_guard2assumption[g]);
            assumptions.insert(assumption);
            s().assign_scoped(assumption);
            m_assumed.insert(g);
        }
        // prefer the search that does not use the limit.
        s().set_phase(~mk_literal(limit()));
        // The predicates of earlier rounds and of enabled guards are spent.
        auto retire = [&](expr* pred) {
            if (m_retired.contains(pred))
                return;
            m_retired.insert(pred);
            ctx.push(insert_obj_trail<expr>(m_retired, pred));
            expr_ref_vector core(m);
            core.push_back(pred);
            push_c(core);
        };
        if (m_num_rounds > 0) {
            app_ref prev = m_util.mk_num_rounds_pred(m_num_rounds - 1);
            m_preds.push_back(prev);
            retire(prev);
        }
        for (expr* g : m_enabled_guards)
            retire(m_guard2assumption[g]);
        // A guard that was assigned true while it was disabled got no body.
        for (unsigned i = 0; i < m_owed.size(); ++i) {
            expr* g = m_owed.get(i);
            if (is_enabled_guard(g) && holds(g))
                expand_body(g);
        }
    }
    
    // see theory_recfun::should_research
    bool solver::should_research(sat::literal_vector const& core) {
        bool found = false;
        ptr_vector<expr> to_enable;
        for (sat::literal lit : core) {
            expr* e = ctx.bool_var2expr(lit.var());
            expr* g = nullptr;
            if (!e)
                continue;
            if (!lit.sign() && m_assumption2guard.find(e, g) && is_disabled_guard(g)) {
                found = true;
                to_enable.push_back(g);
            }
            else if (u().is_num_rounds(e)) 
                found = true;
        }
        if (!found)
            return false;
        ++m_num_rounds;
        if (to_enable.empty())
            for (expr* g : m_certain)
                if (is_disabled_guard(g))
                    to_enable.push_back(g);
        if (to_enable.empty() && m_limited && is_disabled_guard(m_limited))
            to_enable.push_back(m_limited);
        if (to_enable.empty() && !m_disabled_guards.empty())
            to_enable.push_back(m_disabled_guards.back());
        for (expr* g : to_enable) {
            enable_guard(g);
            IF_VERBOSE(2, verbose_stream() << "(smt.recfun :enable-guard " << mk_pp(g, m) << ")\n");
        }
        if (to_enable.empty())
            IF_VERBOSE(2, verbose_stream() << "(smt.recfun :increment-round)\n");
        return true;
    }

    bool solver::is_beta_redex(euf::enode* p, euf::enode* n) const {
        return is_defined(p) || is_case_pred(p);
    }


    bool solver::add_dep(euf::enode* n, top_sort<euf::enode>& dep) {
        if (n->num_args() == 0)
            dep.insert(n, nullptr);
        for (auto* k : euf::enode_args(n))
            dep.add(n, k);
        return true;
    }

    void solver::add_value(euf::enode* n, model& mdl, expr_ref_vector& values) {
        values.set(n->get_root_id(), n->get_root()->get_expr());
    }
    
}
