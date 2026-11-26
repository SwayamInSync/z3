/*++
Copyright (c) 2018 Microsoft Corporation

Module Name:

    theory_recfun.h

Abstract:

    Theory responsible for unrolling recursive functions

Author:

    Simon Cruanes December 2017

Revision History:

--*/
#pragma once

#include "util/scoped_ptr_vector.h"
#include "smt/smt_theory.h"
#include "smt/smt_context.h"
#include "ast/ast_pp.h"
#include "ast/recfun_decl_plugin.h"

namespace smt {

    class theory_recfun : public theory {
        struct stats {
            unsigned m_case_expansions, m_body_expansions, m_macro_expansions;
            void reset() { memset(this, 0, sizeof(stats)); }
            stats() { reset(); }
        };
        
        recfun::decl::plugin&   m_plugin;
        recfun::util&           m_util;
        stats                   m_stats;

        // book-keeping for depth of predicates
        expr_ref_vector          m_disabled_guards; // in the order they were disabled
        obj_hashtable<expr>      m_disabled;        // the same guards, for membership tests
        expr_ref_vector          m_enabled_guards;
        obj_hashtable<expr>      m_enabled;
        expr_ref_vector          m_assumptions;     // one depth-limit predicate per guard ever disabled
        obj_map<expr, expr*>     m_guard2assumption;
        obj_map<expr, expr*>     m_assumption2guard;
        obj_hashtable<expr>      m_assumed;         // disabled guards whose predicate the current round assumes
        expr_ref_vector          m_certain;         // disabled guards true without a decision when the round applied the limit
        expr_ref_vector          m_owed;            // guards assigned true while disabled (scoped with the assignment)
        obj_hashtable<expr>      m_bodied;          // guards whose body is queued (scoped with the queue entry)
        obj_hashtable<expr>      m_retired;         // predicates of enabled guards asserted false (scoped)
        expr*                    m_limited = nullptr; // the last guard that appeared in the current round while the limit was on
        obj_map<expr, unsigned>  m_pred_depth;
        expr_ref_vector          m_preds;
        unsigned_vector          m_preds_lim;
        unsigned                 m_num_rounds { 0 };

        typedef recfun::propagation_item propagation_item;

        scoped_ptr_vector<propagation_item> m_propagation_queue;
        unsigned                            m_qhead { 0 };

        void push_body_expand(expr* e) { push(alloc(propagation_item, alloc(recfun::body_expansion, u(), to_app(e)))); }
        void push_case_expand(expr* e) { push(alloc(propagation_item, alloc(recfun::case_expansion, u(), to_app(e)))); }
        void push_core(expr_ref_vector const& core) { push(alloc(propagation_item, core)); }
        void push(propagation_item* p);

        bool is_enabled_guard(expr* guard) { return m_enabled.contains(guard); }
        bool is_disabled_guard(expr* guard) { return m_disabled.contains(guard); }

        recfun::util & u() const { return m_util; }
        bool is_defined(expr * f) const { return u().is_defined(f); }
        bool is_case_pred(expr * f) const { return u().is_case_pred(f); }

        bool is_defined(enode * e) const { return is_defined(e->get_expr()); }
        bool is_case_pred(enode * e) const { return is_case_pred(e->get_expr()); }

        void activate_guard(expr* guard, expr_ref_vector const& guards);

        expr_ref apply_args(unsigned depth, recfun::vars const & vars, expr_ref_vector const & args, expr * e); //!< substitute variables by args
        void assert_macro_axiom(recfun::case_expansion & e);
        void assert_case_axioms(recfun::case_expansion & e);
        void assert_body_axiom(recfun::body_expansion & e);
        void block_core(expr_ref_vector const& core);
        literal mk_literal(expr* e);

        void disable_guard(expr* guard);
        void enable_guard(expr* guard);
        void expand_body(expr* guard);
        bool has_definition(expr* guard) const;
        bool holds(expr* e);
        app_ref limit() { return m_util.mk_depth_limit_pred(0); }
        app_ref round() { return m_util.mk_num_rounds_pred(m_num_rounds); }
        expr_ref limit_of(expr* guard);
        unsigned get_depth(expr* e);
        void set_depth(unsigned d, expr* e);
        void set_depth_rec(unsigned d, expr* e);
        
        literal mk_eq_lit(expr* l, expr* r);
        bool is_decreasing_order(recfun::vars const& vars) const { 
            return vars.empty() || vars[vars.size()-1]->get_idx() == 0;
        }
    protected:

        bool internalize_atom(app * atom, bool gate_ctx) override;
        bool internalize_term(app * term) override;
        void reset_eh() override;
        void relevant_eh(expr * n) override;
        char const * get_name() const override;
        final_check_status final_check_eh(unsigned) override;
        final_check_status final_check_last_eh() override;
        void assign_eh(bool_var v, bool is_true) override;
        void push_scope_eh() override;
        void pop_scope_eh(unsigned num_scopes) override;
        bool can_propagate() override;
        void propagate() override;
        bool should_research(expr_ref_vector &) override;
        bool is_beta_redex(enode* p, enode* n) const override;

        void new_eq_eh(theory_var v1, theory_var v2) override {}
        void new_diseq_eh(theory_var v1, theory_var v2) override {}
        void add_theory_assumptions(expr_ref_vector & assumptions) override;

    public:
        theory_recfun(context& ctx);
        ~theory_recfun() override;
        theory * mk_fresh(context * new_ctx) override;
        void display(std::ostream & out) const override;
        void collect_statistics(::statistics & st) const override;
    };
}

