/*++
Copyright (c) 2018 Microsoft Corporation, Simon Cruanes

Module Name:

    theory_recfun.cpp

Abstract:

    Theory responsible for unrolling recursive functions

Author:

    Simon Cruanes December 2017

Revision History:

--*/

#include "util/stats.h"
#include "ast/ast_util.h"
#include "ast/ast_ll_pp.h"
#include "ast/for_each_expr.h"
#include "smt/theory_recfun.h"


#define TRACEFN(x) TRACE(recfun, tout << x << '\n';)

namespace smt {

    theory_recfun::theory_recfun(context& ctx)
        : theory(ctx, ctx.get_manager().mk_family_id("recfun")), 
          m_plugin(*reinterpret_cast<recfun::decl::plugin*>(m.get_plugin(get_family_id()))),
          m_util(m_plugin.u()), 
          m_disabled_guards(m),
          m_enabled_guards(m),
          m_assumptions(m),
          m_preds(m) {
        }

    theory_recfun::~theory_recfun() {
        reset_eh();
    }

    char const * theory_recfun::get_name() const { return "recfun"; }

    theory* theory_recfun::mk_fresh(context* new_ctx) {        
        return alloc(theory_recfun, *new_ctx);
    }

    bool theory_recfun::internalize_atom(app * atom, bool gate_ctx) {
        TRACE(recfun, tout << mk_pp(atom, m) << " " << u().has_defs() << "\n");
        if (!u().has_defs()) {
//            if (u().is_defined(atom)) 
//                throw default_exception("recursive atom definition is out of scope");
            return false;
        }
        for (expr * arg : *atom) 
            ctx.internalize(arg, false);
        if (!ctx.e_internalized(atom)) 
            ctx.mk_enode(atom, false, true, true);
        if (!ctx.b_internalized(atom)) 
            ctx.set_var_theory(ctx.mk_bool_var(atom), get_id());
        if (!ctx.relevancy() && u().is_defined(atom)) 
            push_case_expand(atom);
        return true;
    }

    bool theory_recfun::internalize_term(app * term) {
        if (!u().has_defs()) {
//            if (u().is_defined(term)) 
//                throw default_exception("recursive term definition is out of scope");
            return false;
        }
        for (expr* e : *term) {
            ctx.internalize(e, false);
        }
        if (!ctx.e_internalized(term)) {            
            ctx.mk_enode(term, false, false, true);
        }
        if (!ctx.relevancy() && u().is_defined(term)) {
            push_case_expand(term);
        }
        return true; 
    }


    void theory_recfun::reset_eh() {
        m_stats.reset();
        theory::reset_eh();
        m_disabled_guards.reset();
        m_disabled.reset();
        m_enabled_guards.reset();
        m_enabled.reset();
        m_assumptions.reset();
        m_guard2assumption.reset();
        m_assumption2guard.reset();
        m_assumed.reset();
        m_needed.reset();
        m_forced.reset();
        m_forced_budget = 8;
        m_bodied.reset();
        m_retired.reset();
    }

    /*
     * when `n` becomes relevant, if it's `f(t1...tn)` with `f` defined,
     * then case-expand `n`. If it's a macro we can also immediately
     * body-expand it.
     */
    void theory_recfun::relevant_eh(expr * n) {
        SASSERT(ctx.relevancy());
        // TRACEFN("relevant_eh: (defined) " <<  u().is_defined(n) << " " << mk_pp(n, m));        
        if (u().is_defined(n) && u().has_defs()) 
            push_case_expand(n);
    }

    void theory_recfun::push_scope_eh() {
        theory::push_scope_eh();
        m_preds_lim.push_back(m_preds.size());
    }

    void theory_recfun::pop_scope_eh(unsigned num_scopes) {
        theory::pop_scope_eh(num_scopes);
        
        // restore depth book-keeping
        unsigned new_lim = m_preds_lim.size()-num_scopes;
#if 0
        // depth tracking of recursive unfolding is 
        // turned off when enabling this code:
        unsigned start = m_preds_lim[new_lim];
        for (unsigned i = start; i < m_preds.size(); ++i) {
            m_pred_depth.remove(m_preds.get(i));
        }
        m_preds.resize(start);
#endif
        m_preds_lim.shrink(new_lim);
    }
         
    bool theory_recfun::can_propagate() {
        return m_qhead < m_propagation_queue.size();
    }
    
    void theory_recfun::propagate() {
        if (m_qhead == m_propagation_queue.size())
            return;
        ctx.push_trail(value_trail<unsigned>(m_qhead));
        // Yield to the context's resource checks before processing newly queued expansions.
        for (unsigned end = m_propagation_queue.size(); m_qhead < end && !ctx.inconsistent(); ++m_qhead) {
            auto& p = *m_propagation_queue[m_qhead];
            if (p.is_core()) 
                block_core(p.core());
            else if (p.is_case()) 
                assert_case_axioms(p.case_ex());
            else 
                assert_body_axiom(p.body());
        }
    }

    void theory_recfun::push(propagation_item* p) {
        m_propagation_queue.push_back(p);         
        ctx.push_trail(push_back_vector<scoped_ptr_vector<propagation_item>>(m_propagation_queue));        
    }


    bool theory_recfun::has_definition(expr* guard) const {
        return m_plugin.has_case_def(to_app(guard)->get_decl());
    }

    bool theory_recfun::holds(expr* e) {
        return ctx.b_internalized(e) && ctx.get_assignment(ctx.get_literal(e)) == l_true;
    }

    /**
     * The predicate that limits `guard` in the current round: its own
     * assumption when the round assumes it, and the round predicate for a
     * guard that was disabled after the round started.
     */
    expr_ref theory_recfun::limit_of(expr* guard) {
        if (m_assumed.contains(guard))
            return expr_ref(m_guard2assumption[guard], m);
        return expr_ref(round(), m);
    }

    /**
     * The guard appears at a depth below the current cutoff: it keeps its
     * definition but gets no body.
     *
     * The depth limit is lazy. The clauses added here are
     *   `limit & p => ~guard`      for each predicate p that limits the guard,
     * where `limit` is a predicate that no round assumes. They take effect
     * when final_check_eh adds `round => limit`, which it does when an
     * assignment that every theory accepts sets a disabled guard to true: the
     * search then needs an unfolding below the cutoff, and the limit applies
     * to every disabled guard for the rest of the round.
     *
     * Asserting `round => ~guard` up front, and assuming `~guard` in later
     * rounds, makes whatever the base cases imply (such as a bound `n <= 2`
     * on the recursion argument) a consequence of the limit before the search
     * starts. A refutation that uses such a consequence puts the limit into
     * the unsat core although a refutation without it exists, and the solver
     * then unfolds deeper without end.
     *
     * The clause is queued with the case expansion of the call, so it lives
     * exactly as long as the guard's other axioms.
     */
    void theory_recfun::disable_guard(expr* guard) {
        SASSERT(!is_enabled_guard(guard));
        if (!m_guard2assumption.contains(guard)) {
            app_ref assumption = m_util.mk_depth_limit_pred(m_assumptions.size() + 1);
            m_assumptions.push_back(assumption);
            m_guard2assumption.insert(guard, assumption);
            m_assumption2guard.insert(assumption, guard);
            m_disabled_guards.push_back(guard);
            m_disabled.insert(guard);
        }
        // The guard's own predicate limits it in every round that assumes it.
        // A round that disables the guard has not assumed it, so that round's
        // predicate limits it as well.
        expr_ref_vector core(m);
        core.push_back(limit());
        core.push_back(m_guard2assumption[guard]);
        core.push_back(guard);
        TRACEFN("add core: " << core);
        push_core(core);
        if (!m_assumed.contains(guard)) {
            core[1] = round();
            TRACEFN("add core: " << core);
            push_core(core);
        }
    }

    void theory_recfun::enable_guard(expr* guard) {
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
    void theory_recfun::expand_body(expr* guard) {
        if (m_bodied.contains(guard) || !has_definition(guard))
            return;
        m_bodied.insert(guard);
        ctx.push_trail(insert_obj_trail<expr>(m_bodied, guard));
        push_body_expand(guard);
    }

    /**
     * retrieve depth associated with predicate or expression.
     */
    unsigned theory_recfun::get_depth(expr* e) {
        SASSERT(u().is_defined(e) || u().is_case_pred(e));
        unsigned d = 0;
        m_pred_depth.find(e, d);
        return d;
    }

    /**
     * Update depth of subterms of e with respect to d.
     */
    void theory_recfun::set_depth_rec(unsigned d, expr* e) {
        struct insert_c {
            theory_recfun& th;
            unsigned m_depth;
            insert_c(theory_recfun& th, unsigned d): th(th), m_depth(d) {}
            void operator()(app* e) { th.set_depth(m_depth, e); }
            void operator()(quantifier*) {}
            void operator()(var*) {}
        };
        insert_c proc(*this, d);
        for_each_expr(proc, e);
    }

    void theory_recfun::set_depth(unsigned depth, expr* e) {        
        if ((u().is_defined(e) || u().is_case_pred(e)) && !m_pred_depth.contains(e)) {
            m_pred_depth.insert(e, depth);
            m_preds.push_back(e);
        }
    }

    /**
     * A disabled guard that is true at the search level is true in every
     * assignment of the round. It is unfolded at once, as it is without a
     * depth limit, and enabled when the round ends. One such unfolding can
     * force the next without end, so a round has a budget of them.
     */
    bool theory_recfun::is_forced(expr* guard) {
        if (ctx.get_scope_level() > ctx.get_search_level() || m_forced.size() >= m_forced_budget)
            return false;
        m_forced.push_back(guard);
        return true;
    }

    /**
     * if `is_true` and `v = C_f_i(t1...tn)`, 
     *    then body-expand i-th case of `f(t1...tn)`
     * unless the guard is disabled: final_check_eh then decides.
     */
    void theory_recfun::assign_eh(bool_var v, bool is_true) {
        expr* e = ctx.bool_var2expr(v);
        if (is_true && u().is_case_pred(e)) {
            TRACEFN("assign_case_pred_true " << v << " " << mk_pp(e, m));
            if (!is_disabled_guard(e) || is_forced(e))
                expand_body(e);
        }
    }

     // replace `vars` by `args` in `e`
    expr_ref theory_recfun::apply_args(
        unsigned depth,
        recfun::vars const & vars,
        expr_ref_vector const & args,
        expr * e) {
        var_subst subst(m, true);
        expr_ref new_body = subst(e, args);
        ctx.get_rewriter()(new_body); // simplify
        set_depth_rec(depth + 1, new_body);
        return new_body;
    }
        
    literal theory_recfun::mk_literal(expr* e) {
        bool is_not = m.is_not(e, e);
        ctx.internalize(e, false);
        literal lit = ctx.get_literal(e);
        ctx.mark_as_relevant(lit);
        if (is_not)
            lit.neg();
        return lit;
    }


    // lambdas are quantifier nodes, but they are first-class array terms for the
    // solver; only forall/exists need to be tunnelled through a fresh Boolean.
    static bool has_real_quantifiers(expr* e) {
        if (!has_quantifiers(e))
            return false;
        struct proc {
            bool m_found = false;
            void operator()(quantifier* q) { if (!is_lambda(q)) m_found = true; }
            void operator()(app*) {}
            void operator()(var*) {}
        };
        proc p;
        for_each_expr(p, e);
        return p.m_found;
    }

    literal theory_recfun::mk_eq_lit(expr* l, expr* r) {
        literal lit;
        if (has_real_quantifiers(l) || has_real_quantifiers(r)) {
            expr_ref eq1(m.mk_eq(l, r), m);
            expr_ref fn(m.mk_fresh_const("rec-eq", m.mk_bool_sort()), m);
            expr_ref eq(m.mk_eq(fn, eq1), m);
            ctx.add_asserted(eq);
            ctx.internalize_assertions();
            lit = mk_literal(fn);
        }
        else {
            if (m.is_true(r) || m.is_false(r))
                std::swap(l, r);
            if (m.is_true(l))
                lit = mk_literal(r);
            else if (m.is_false(l))
                lit = ~mk_literal(r);
            else
                lit = mk_eq(l, r, false);
        }
        ctx.mark_as_relevant(lit);
        return lit;
    }

    void theory_recfun::block_core(expr_ref_vector const& core) {
        literal_vector clause;
        for (expr* e : core)
            clause.push_back(~mk_literal(e));
        ctx.mk_th_axiom(get_id(), clause);
    }

    /**
     * For functions f(args) that are given as macros f(vs) = rhs
     * 
     * 1. substitute `e.args` for `vs` into the macro rhs
     * 2. add unit clause `f(args) = rhs`
     */
    void theory_recfun::assert_macro_axiom(recfun::case_expansion & e) {
        m_stats.m_macro_expansions++;
        TRACEFN("case expansion " << e);
        SASSERT(e.m_def->is_fun_macro());
        auto & vars = e.m_def->get_vars();
        expr_ref lhs(e.m_lhs, m);
        unsigned depth = get_depth(e.m_lhs);
        expr_ref rhs(apply_args(depth, vars, e.m_args, e.m_def->get_rhs()), m);
        literal lit = mk_eq_lit(lhs, rhs);
        std::function<literal(void)> fn = [&]() { return lit; };
        scoped_trace_stream _tr(*this, fn);
        ctx.mk_th_axiom(get_id(), 1, &lit);
        TRACEFN("macro expansion yields " << pp_lit(ctx, lit));
    }

    /**
     * Add case axioms for every case expansion path.
     *
     * assert `p(args) <=> And(guards)` (with CNF on the fly)
     *
     * also body-expand paths that do not depend on any defined fun
     */
    void theory_recfun::assert_case_axioms(recfun::case_expansion & e) {

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
        literal_vector preds;
        auto & vars = e.m_def->get_vars();
            
        for (recfun::case_def const & c : e.m_def->get_cases()) {
            // applied predicate to `args`
            app_ref pred_applied = c.apply_case_predicate(e.m_args);
            SASSERT(u().owns_app(pred_applied));
            literal concl = mk_literal(pred_applied);
            preds.push_back(concl);

            unsigned depth = get_depth(e.m_lhs);
            set_depth(depth, pred_applied);
            expr_ref_vector guards(m);
            for (auto & g : c.get_guards()) {
                guards.push_back(apply_args(depth, vars, e.m_args, g));
            }
            if (c.is_immediate()) {
                recfun::body_expansion be(pred_applied, c, e.m_args);
                assert_body_axiom(be);            
            }
            else if (!is_enabled_guard(pred_applied)) 
                disable_guard(pred_applied);
            // A disabled guard keeps its definition: it is true exactly when
            // its case applies, so a true disabled guard means that the
            // assignment needs an unfolding below the cutoff.
            activate_guard(pred_applied, guards);
        }

        TRACEFN("assert cases " << preds);
        // the disjunction of branches is asserted
        // to close the available cases. 

        scoped_trace_stream _tr(*this, preds);
        ctx.mk_th_axiom(get_id(), preds);       
    }

    void theory_recfun::activate_guard(expr* pred_applied, expr_ref_vector const& guards) {
        literal concl = mk_literal(pred_applied);
        literal_vector lguards;
        lguards.push_back(concl);
        for (expr* ga : guards) {
            literal guard = mk_literal(ga);
            lguards.push_back(~guard);
            scoped_trace_stream _tr1(*this, ~concl, guard);
            ctx.mk_th_axiom(get_id(), ~concl, guard);
        }
        scoped_trace_stream _tr2(*this, lguards);
        ctx.mk_th_axiom(get_id(), lguards);        
    }

    /**
     * For a guarded definition guards => f(vars) = rhs
     * and occurrence f(args)
     *
     * substitute `args` for `vars` in guards, and rhs
     * add axiom guards[args/vars] => f(args) = rhs[args/vars]
     *
     */
    void theory_recfun::assert_body_axiom(recfun::body_expansion & e) {
        ++m_stats.m_body_expansions;
        recfun::def & d = *e.m_cdef->get_def();
        auto & vars = d.get_vars();
        auto & args = e.m_args;
        unsigned depth = get_depth(e.m_pred);
        expr_ref lhs(u().mk_fun_defined(d, args), m);
        expr_ref rhs = apply_args(depth, vars, args, e.m_cdef->get_rhs());
        if (has_real_quantifiers(rhs)) {
            expr_ref fn(m.mk_fresh_const("rec-eq", rhs->get_sort()), m);
            expr_ref eq(m.mk_eq(fn, rhs), m);
            ctx.assert_expr(eq);
            ctx.internalize_assertions();
            rhs = fn;
        }
        literal_vector clause;
        for (auto & g : e.m_cdef->get_guards()) {
            expr_ref guard = apply_args(depth, vars, args, g);
            clause.push_back(~mk_literal(guard));
            if (clause.back() == true_literal) {
                TRACEFN("body " << e << "\n" << clause << "\n" << guard);
                return;
            }
            if (clause.back() == false_literal) {
                clause.pop_back();
            }
        }        
        clause.push_back(mk_eq_lit(lhs, rhs));
        TRACEFN(e << "\n" << pp_lits(ctx, clause));
        std::function<literal_vector(void)> fn = [&]() { return clause; };
        scoped_trace_stream _tr(*this, fn);
        ctx.mk_th_axiom(get_id(), clause);
    }
    
    /**
     * The context runs the second level once no theory and not the quantifier
     * manager asked to continue at the first, which is when the depth limit
     * has to decide about the assignment.
     */
    final_check_status theory_recfun::final_check_eh(unsigned level) {
        if (can_propagate()) {
            TRACEFN("final\n");
            propagate();
            return FC_CONTINUE;
        }
        if (m_lazy && holds(round()) && charge_lazy()) {
            turn_limit_on();
            return FC_CONTINUE;
        }
        if (!needs_limit())
            return FC_DONE;
        return level == 1 ? FC_GIVEUP : apply_limit();
    }

    void theory_recfun::restart_eh() {
        if (m_lazy && holds(round()) && charge_lazy())
            turn_limit_on();
    }

    /**
     * Account for what the round spent without the limit; true if that
     * exhausts the allowance.
     */
    bool theory_recfun::charge_lazy() {
        uint64_t count = m.limit().count();
        m_lazy_cost += cost_since(m_lazy_start);
        m_lazy_start = count;
        return lazy_exhausted();
    }

    uint64_t theory_recfun::cost_since(uint64_t start) const {
        uint64_t count = m.limit().count();
        return count > start ? count - start : 0;
    }

    /**
     * Looking for an assignment without the limit can cost far more than
     * refuting the assertions with it. So the searches without the limit
     * spend, in total, no more than the searches with the limit have spent,
     * and a fixed amount to start with.
     */
    bool theory_recfun::lazy_exhausted() const {
        return m_lazy_cost >= m_limited_cost + m_lazy_allowance;
    }

    void theory_recfun::turn_limit_on() {
        m_lazy = false;
        m_limit_start = m.limit().count();
        expr_ref_vector core(m);
        core.push_back(round());
        core.push_back(m.mk_not(limit()));
        push_core(core);
    }

    bool theory_recfun::needs_limit() {
        for (expr* g : m_disabled_guards)
            if (holds(g) && has_definition(g) && !m_bodied.contains(g))
                return true;
        return false;
    }

    /**
     * The assignment is accepted by every theory. A disabled guard that is
     * true in it and has no body relies on an unfolding below the current
     * cutoff.
     *
     * If the round assumes the guard's limit predicate, the limit applies:
     * `round => limit` turns the limit on for every disabled guard, and
     * `limit_of(guard) => ~guard` is false in this assignment, so the search
     * always makes progress, whatever became of the guard's queued clause.
     *
     * If the predicate is not assumed (a search that did not go through
     * add_theory_assumptions, as the second phase of get_consequences), there
     * is no limit to apply and the guard is unfolded, as it always was.
     */
    final_check_status theory_recfun::apply_limit() {
        bool unfolded = false;
        for (expr* g : m_disabled_guards) {
            if (!holds(g) || !has_definition(g) || m_bodied.contains(g))
                continue;
            expr_ref lim = limit_of(g);
            if (!holds(lim)) {
                TRACEFN("unfold without a limit: " << mk_pp(g, m));
                expand_body(g);
                unfolded = true;
                continue;
            }
            TRACEFN("apply the depth limit: " << mk_pp(g, m));
            // an unsat core that has the round predicate does not name the guard.
            if (!m_assumed.contains(g))
                m_needed.push_back(g);
            expr_ref_vector core(m);
            if (!holds(limit())) {
                for (expr* h : m_disabled_guards)
                    if (holds(h) && has_definition(h) && ctx.get_assign_level(ctx.get_literal(h)) <= ctx.get_search_level())
                        m_needed.push_back(h);
                if (m_lazy) {
                    charge_lazy();
                    m_lazy = false;
                    m_limit_start = m.limit().count();
                }
                core.push_back(round());
                core.push_back(m.mk_not(limit()));
                block_core(core);
                core.reset();
            }
            if (!ctx.inconsistent()) {
                core.push_back(lim);
                core.push_back(g);
                block_core(core);
            }
            SASSERT(ctx.inconsistent());
            return FC_CONTINUE;
        }
        return unfolded ? FC_CONTINUE : FC_DONE;
    }

    /**
     * Start a round: assume the round predicate and the predicate of every
     * disabled guard, and restore what the guards need in the current scope.
     * Everything queued here lives until the user scope is popped; the scoped
     * sets make sure it is queued once per scope and again after a pop.
     */
    void theory_recfun::add_theory_assumptions(expr_ref_vector & assumptions) {
        if (!u().has_rec_defs() && m_disabled_guards.empty())
            return;
        app_ref dlimit = round();
        TRACEFN("add_theory_assumption " << dlimit);
        assumptions.push_back(dlimit);
        m_assumed.reset();
        m_needed.reset();
        m_forced.reset();
        m_lazy = true;
        m_lazy_start = m.limit().count();
        for (expr* g : m_disabled_guards) {
            assumptions.push_back(m_guard2assumption[g]);
            m_assumed.insert(g);
        }
        // prefer the search that does not use the limit.
        ctx.force_phase(~mk_literal(limit()));
        // The predicates of earlier rounds and of enabled guards are spent.
        // Their clauses stay; falsify them so that they cannot limit anything.
        auto retire = [&](expr* pred) {
            if (m_retired.contains(pred))
                return;
            m_retired.insert(pred);
            ctx.push_trail(insert_obj_trail<expr>(m_retired, pred));
            expr_ref_vector core(m);
            core.push_back(pred);
            push_core(core);
        };
        if (m_num_rounds > 0) {
            app_ref prev = m_util.mk_num_rounds_pred(m_num_rounds - 1);
            m_preds.push_back(prev);
            retire(prev);
        }
        for (expr* g : m_enabled_guards)
            retire(m_guard2assumption[g]);
        // A guard that is true since before it was enabled has no body.
        for (expr* g : m_enabled_guards)
            if (holds(g))
                expand_body(g);
        if (lazy_exhausted())
            turn_limit_on();
    }

    /**
     * if `dlimit` or the predicate of a disabled guard occurs in the unsat
     * core, return 'true' and enable guards for the next round.
     *
     * Every disabled guard named by the core blocked the refutation of the
     * current round, so all of them are enabled at once: enabling one guard per
     * round costs one re-search per guard, which is prohibitive for models that
     * need hundreds of unfoldings (e.g. well-formedness predicates over long
     * lists and nested datatypes). So are the guards that every assignment of
     * the round sets to true.
     *
     * When that enables nothing, the conflict used the round predicate, which
     * limits the guards disabled during the round and does not tell which of
     * them: they are all enabled. Enabling one of them can unfold one call
     * without end while the call that the search needs stays limited.
     */
    bool theory_recfun::should_research(expr_ref_vector & unsat_core) {
        bool found = false;
        unsigned num_enabled = 0;
        auto enable = [&](expr* g) {
            if (!is_disabled_guard(g))
                return;
            enable_guard(g);
            ++num_enabled;
            IF_VERBOSE(2, verbose_stream() << "(smt.recfun :enable-guard " << mk_pp(g, m) << ")\n");
        };
        ptr_vector<expr> named;
        for (auto * ne : unsat_core) {
            expr* e = nullptr;
            if (m_assumption2guard.find(ne, e) && is_disabled_guard(e)) {
                found = true;
                named.push_back(e);
            }
            else if (u().is_num_rounds(ne)) 
                found = true;
        }
        if (!found)
            return false;
        m_num_rounds++;
        if (m_lazy)
            charge_lazy();
        else
            m_limited_cost += cost_since(m_limit_start);
        for (expr* g : named)
            enable(g);
        for (expr* g : m_forced)
            enable(g);
        if (m_forced.size() >= m_forced_budget)
            m_forced_budget *= 2;
        if (num_enabled == 0)
            for (expr* g : m_needed)
                enable(g);
        if (num_enabled == 0) {
            ptr_vector<expr> limited;
            for (expr* g : m_disabled_guards)
                if (!m_assumed.contains(g))
                    limited.push_back(g);
            for (expr* g : limited)
                enable(g);
        }
        if (num_enabled == 0 && !m_disabled_guards.empty())
            enable(m_disabled_guards.back());
        if (num_enabled == 0)
            IF_VERBOSE(2, verbose_stream() << "(smt.recfun :increment-round " << m_num_rounds << ")\n");
        TRACEFN("should research " << found);
        return true;
    }

    /**
     * n is an argument of p, if p is a function definition or case predicate,
     * then there is no reason for the solver to enforce that equality on n is 
     * fully determined. It is a beta-redex with respect to expanding p.
     */
    bool theory_recfun::is_beta_redex(enode* p, enode* n) const {
        return is_defined(p) || is_case_pred(p);
    }

    void theory_recfun::display(std::ostream & out) const {
        out << "recfun\n";
        out << "disabled guards:\n" << m_disabled_guards << "\n";
        out << "enabled guards:\n" << m_enabled_guards << "\n";
    }

    void theory_recfun::collect_statistics(::statistics & st) const {
        st.update("recfun macro expansion", m_stats.m_macro_expansions);
        st.update("recfun case expansion", m_stats.m_case_expansions);
        st.update("recfun body expansion", m_stats.m_body_expansions);
    }

}
