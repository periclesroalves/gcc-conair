/* Concurrency bug recovery via single-threaded idempotent execution.
   Written by Pericles Alves <pericles@cs.wisc.edu>

This file is part of GCC.

GCC is free software; you can redistribute it and/or modify it
under the terms of the GNU General Public License as published by the
Free Software Foundation; either version 3, or (at your option) any
later version.

GCC is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
for more details.

You should have received a copy of the GNU General Public License
along with GCC; see the file COPYING3.  If not see
<http://www.gnu.org/licenses/>.  */

/* This file implements concurrency bug recovery instrumentation.

   References:

     ConAir: Featherweight Concurrency Bug Recovery Via
     Single-Threaded Idempotent Execution, Wei Zhang, Marc de Kruijf,
     Ang Li, Shan Lu, Karthikeyan Sankaralingam, ASPLOS, 2013.

   The algorithm is divided into three main steps:

     (1) Failure site identification.

     (2) Reexecution point identification.

     (3) Rollback instrumentation.  */

#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "tm.h"
#include "tree.h"
#include "print-tree.h"
#include "flags.h"
#include "basic-block.h"
#include "function.h"
#include "gimple-pretty-print.h"
#include "pointer-set.h"
#include "tree-ssa-alias.h"
#include "internal-fn.h"
#include "tree-eh.h"
#include "gimple-expr.h"
#include "is-a.h"
#include "gimple.h"
#include "gimplify.h"
#include "gimple-iterator.h"
#include "gimple-ssa.h"
#include "tree-cfg.h"
#include "tree-phinodes.h"
#include "ssa-iterators.h"
#include "stringpool.h"
#include "tree-ssanames.h"
#include "tree-pass.h"

/* Inserts an assertion before the dereference pointed by GSI in block BB to
   verify that ADDR_VAR holds a somewhat valid address.
    
                                 |
        |                 ______\|/_______
     __\|/___            |      ...       |
    |   ...  |           | if (p == NULL) |
    | a = *p |           |________________|
    |   ...  |   --->        |      |___________
    |________|               |     T     ______\|/______
        |                  F |          | __assert_fail |
       \|/                   |          |_______________|
                             |  ________________|
                         _\|/_\|/_
                        |  a = *p |
                        |   ...   |
                        |_________|
                             |
                            \|/
*/

static void
insert_deref_assert(gimple_stmt_iterator *gsi, tree addr_var)
{
  gimple cond;
  edge e_true, e_false;
  basic_block bb_cond, bb_assert, bb_deref;

  bb_cond = gsi_bb (*gsi); 
  cond = gimple_build_cond (EQ_EXPR, addr_var, null_pointer_node, NULL_TREE, NULL_TREE);
  gsi_insert_before (gsi, cond, GSI_SAME_STMT);
  e_true = split_block (bb_cond, cond);
  bb_deref = e_true->dest;
  bb_assert = split_edge (e_true);
  e_true = single_succ_edge (bb_cond);
  e_false = make_edge (bb_cond, bb_deref, EDGE_FALSE_VALUE);

  e_true->flags &= ~EDGE_FALLTHRU;
  e_true->flags |= EDGE_TRUE_VALUE;

  set_immediate_dominator (CDI_DOMINATORS, bb_assert, bb_cond);
  set_immediate_dominator (CDI_DOMINATORS, bb_deref, bb_cond);

  // DBG
  gimple_stmt_iterator gsi2 = gsi_last_bb (bb_assert);
  gsi_insert_after (&gsi2, gimple_build_nop (), GSI_NEW_STMT);
  // DBG

  // TODO:
  // . Test if the rest of the block is processed after a given stmt in the
  //    block is processed.
  // . Update profile info.
  // . Insert assertion failure in bb_assert.

  *gsi = gsi_last_bb (bb_cond);
}

/* Tranforms every other kind of failure point in assertion failures, so that
 * they can be handled in the same way later. */

static void
simplify_failure_sites ()
{
  basic_block bb;
  gimple_stmt_iterator gsi;
  gimple stmt;
  struct pointer_set_t *simplified_stmts;

  simplified_stmts = pointer_set_create ();

  FOR_EACH_BB_FN (bb, cfun)
    {
      // TODO: verify if we need phi iteration for a given kind of FP.
      for (gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi))
    {
      stmt = gsi_stmt (gsi);

      // TODO: Verify builtins that dereference memory.

      if (is_gimple_assign (stmt) && gimple_assign_single_p (stmt)) {
        tree lhs = gimple_assign_lhs (stmt);
        tree rhs = gimple_assign_rhs1 (stmt);
        enum tree_code lhs_code = TREE_CODE (lhs);
        enum tree_code rhs_code = TREE_CODE (rhs);
        tree addr_var;

        if (TREE_CODE_CLASS (lhs_code) == tcc_reference)
            addr_var = TREE_OPERAND (lhs, 0);
        else if (TREE_CODE_CLASS (rhs_code) == tcc_reference)
            addr_var = TREE_OPERAND (rhs, 0);
        else
            continue;

        if ((TREE_CODE (addr_var) == SSA_NAME)
          && !pointer_set_contains (simplified_stmts, stmt)) {
            insert_deref_assert(&gsi, addr_var);
            pointer_set_insert (simplified_stmts, stmt);
        }
      }
    }
    }

  pointer_set_destroy (simplified_stmts);
}

/* Main entry point for concurrency bug recovery instrumentation.  */

static unsigned int
do_conair (void)
{
  simplify_failure_sites ();





  basic_block bb;
  gimple_stmt_iterator gsi;
  gimple stmt;

  FOR_EACH_BB_FN (bb, cfun)
    {
      // TODO: verify if we need phi iteration for a given kind of FP.
      for (gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi))
    {
      stmt = gsi_stmt (gsi);
      
      if (is_gimple_call (stmt)) {
          tree fndecl = gimple_call_fndecl (stmt);

          if ((fndecl != NULL_TREE) && (strncmp (IDENTIFIER_POINTER (DECL_NAME (fndecl)), "__assert_rtn", 12) == 0))
              printf ("found assert failure!\n");
      }
      
    }
    }


  return 0;
}

static bool
gate_conair (void)
{
  return flag_conair != 0;
}

namespace {

const pass_data pass_data_conair =
{
  GIMPLE_PASS, /* type */
  "conair", /* name */
  OPTGROUP_NONE, /* optinfo_flags */
  true, /* has_gate */
  true, /* has_execute */
  TV_CONAIR, /* tv_id */
  ( PROP_cfg | PROP_ssa ), /* properties_required */
  0, /* properties_provided */
  0, /* properties_destroyed */
  0, /* todo_flags_start */
  ( TODO_verify_ssa | TODO_cleanup_cfg
    | TODO_update_ssa ), /* todo_flags_finish */
};

class pass_conair : public gimple_opt_pass
{
public:
  pass_conair (gcc::context *ctxt)
    : gimple_opt_pass (pass_data_conair, ctxt)
  {}

  /* opt_pass methods: */
  opt_pass * clone () { return new pass_conair (m_ctxt); }
  bool gate () { return gate_conair (); }
  unsigned int execute () { return do_conair (); }

}; // class pass_conair

} // anon namespace

gimple_opt_pass *
make_pass_conair (gcc::context *ctxt)
{
  return new pass_conair (ctxt);
}
