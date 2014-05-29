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

     [1] Wei Zhang, Marc de Kruijf, Ang Li, Shan Lu, Karthikeyan Sankaralingam,
     "ConAir: Featherweight Concurrency Bug Recovery Via Single-Threaded
     Idempotent Execution", ASPLOS, 2013.

     [2] Marc de Kruijf, Karthikeyan Sankaralingam, and Somesh Jha, "Static
     Analysis and Compiler Design for Idempotent Processing", PLDI, 2012.

   The algorithm is divided into three main steps:

     (1) Failure site identification.

     (2) Reexecution point identification.

     (3) Rollback instrumentation.  */

#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "tm.h"
#include "tree.h"
#include "tree-nested.h"
#include "print-tree.h"
#include "flags.h"
#include "bitmap.h"
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
#include "cgraph.h"
#include "gimplify.h"
#include "gimple-iterator.h"
#include "gimple-ssa.h"
#include "tree-cfg.h"
#include "tree-phinodes.h"
#include "ssa-iterators.h"
#include "stringpool.h"
#include "tree-ssanames.h"
#include "tree-pass.h"
#include "cfgloop.h"

#define MAX_REEXEC_COUNT 10000

static struct pointer_set_t *reexec_points;
static bitmap headers_with_checkpoints;
static bitmap cut_loops;
static bool sjlj_infra_initialized;
static tree j_buffer;
static tree reexec_counter;
static gimple reexec_counter_reset_stmt;
static basic_block dispatcher_bb;


/* Make sure that the infrastructure needed for setjmp/longjmp insertion is
   initialized  */

static void
prepare_sjlj_infra ()
{
  gimple dispatcher_call;
  gimple_stmt_iterator dispatcher_gsi, decl_gsi;

  if (sjlj_infra_initialized)
    return;

  cfun->calls_setjmp = true;
  cfun->has_nonlocal_label = 1;

  // Initialize a 5 word local buffer to be used by setjmp and longjmp.
  tree size = size_int (5 * BITS_PER_WORD / POINTER_SIZE - 1);
  tree index = build_index_type (size);
  tree type = build_array_type (ptr_type_node, index);

  j_buffer = build_decl (DECL_SOURCE_LOCATION (current_function_decl),
    VAR_DECL, get_identifier ("__conair_j_buf"), type);
  DECL_CONTEXT (j_buffer) = current_function_decl;
  DECL_ARTIFICIAL (j_buffer) = 1;
  TREE_ADDRESSABLE (j_buffer) = 1;
  TREE_STATIC (j_buffer) = 0;
  DECL_EXTERNAL (j_buffer) = 0;
  TREE_READONLY (j_buffer) = 0;
  TREE_THIS_VOLATILE (j_buffer) = 0;
  add_local_decl (cfun, j_buffer);

  // Create and insert a dispatcher block to receive all abnormal edges.
  dispatcher_bb = create_empty_bb (ENTRY_BLOCK_PTR_FOR_FN (cfun));
  dispatcher_bb->loop_father = ENTRY_BLOCK_PTR_FOR_FN (cfun)->loop_father;
  dispatcher_gsi = gsi_start_bb (dispatcher_bb);
  dispatcher_call = gimple_build_call_internal (IFN_ABNORMAL_DISPATCHER, 1,
    boolean_false_node);
  gsi_insert_after (&dispatcher_gsi, dispatcher_call, GSI_NEW_STMT);

  // Create and initialize the reexecution counter.
  reexec_counter = build_decl (DECL_SOURCE_LOCATION (current_function_decl),
    VAR_DECL, get_identifier ("__conair_reexec_counter"), unsigned_type_node);
  DECL_CONTEXT (reexec_counter) = current_function_decl;
  DECL_ARTIFICIAL (reexec_counter) = 1;
  DECL_GIMPLE_REG_P (reexec_counter) = 1;
  TREE_READONLY (reexec_counter) = 0;
  DECL_EXTERNAL (reexec_counter) = 0;
  TREE_STATIC (reexec_counter) = 0;
  TREE_ADDRESSABLE (reexec_counter) = 0;
  TREE_THIS_VOLATILE (reexec_counter) = 0;
  add_local_decl (cfun, reexec_counter);

  reexec_counter_reset_stmt = gimple_build_assign (reexec_counter,
    build_int_cst (unsigned_type_node, 0));
  decl_gsi = gsi_start_bb (single_succ_edge (ENTRY_BLOCK_PTR_FOR_FN
    (cfun))->dest);
  gsi_insert_before (&decl_gsi, reexec_counter_reset_stmt, GSI_SAME_STMT);

  sjlj_infra_initialized = true;
}


/* Create an abnormal edge from every effectful call to the dispatcher block.
   We assume that effectful calls that already are the last instruction in a
   block do not need any modification. Note that blocks are split if needed.  */

static void
link_effectful_calls ()
{
  gimple stmt;
  gimple_stmt_iterator gsi;
  basic_block bb;

  // TODO: test this function.

  FOR_EACH_BB_FN (bb, cfun)
    {
      bool should_end_bb = false;
      gimple prev_stmt;

      for (gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi))
    {
      stmt = gsi_stmt(gsi);

      if (should_end_bb) {
        edge e = split_block (bb, prev_stmt);
        make_edge (e->src, dispatcher_bb, EDGE_ABNORMAL);
      }

      should_end_bb = is_gimple_call (stmt) && gimple_has_side_effects (stmt);

      if (should_end_bb)
        prev_stmt = stmt;
    }
    }
}


/* Insert a stjmp call before GSI. Example:

                         |
                     ___\|/___
     |              | setup() |         ______________
   _\|/__           |_________|   ____\|/_____        |
  | STMT |    --->       |       | receiver() |       |
  |______|               |       |____________|       |
     |                   |    _______|     |          |
    \|/                _\|/_\|/_     _____\|/______   |
                      |  STMT   |   | DISPATCHER() |  |
                      |_________|   |______________|  |
                           |               |__________|
                          \|/              abnormal flow
*/

static void
insert_setjmp_before (gimple_stmt_iterator gsi)
{
  tree receiver_label = create_artificial_label (UNKNOWN_LOCATION);
  gimple_stmt_iterator receiver_gsi;
  tree label_addr, buf_addr;
  basic_block setup_bb, receiver_bb, cont_bb;
  gimple setup_call, receiver_call, label_stmt;
  edge cont_e;

  FORCED_LABEL (receiver_label) = 1;

  // Build '__builtin_setjmp_setup (j_BUFFER, RECEIVER_LABEL)' and insert.
  label_addr = build_addr (receiver_label, current_function_decl);
  buf_addr = build1 (ADDR_EXPR, build_pointer_type (ptr_type_node), j_buffer);
  setup_call = gimple_build_call (builtin_decl_explicit (BUILT_IN_SETJMP_SETUP),
    2, buf_addr, label_addr);
  gsi_insert_before (&gsi, setup_call, GSI_SAME_STMT);

  // Make different blocks for setup and receiver calls.
  cont_e = split_block (gsi_bb (gsi), setup_call);
  setup_bb = cont_e->src;
  cont_bb = cont_e->dest;
  receiver_bb = split_edge (cont_e);
  redirect_edge_succ (single_succ_edge (setup_bb), cont_bb);

  // Build 'RECEIVER_LABEL:' and insert.
  receiver_gsi = gsi_start_bb (receiver_bb);
  label_stmt = gimple_build_label (receiver_label);
  gsi_insert_after (&receiver_gsi, label_stmt, GSI_NEW_STMT);

  // Build '__builtin_setjmp_receiver (RECEIVER_LABEL)' and insert.
  receiver_call = gimple_build_call (builtin_decl_explicit (BUILT_IN_SETJMP_RECEIVER), 1,
    label_addr);
  gsi_insert_after (&receiver_gsi, receiver_call, GSI_NEW_STMT);

  make_edge (dispatcher_bb, receiver_bb, EDGE_ABNORMAL);
  make_edge (receiver_bb, dispatcher_bb, EDGE_ABNORMAL);
}


/* Instrument the reexecution point STMT with a setjmp call.  */

static bool
instrument_reexec_point (const void *stmt_ptr, void *data ATTRIBUTE_UNUSED)
{
  gimple stmt;
  gimple_stmt_iterator gsi;
  basic_block bb;
  edge e;
  edge_iterator ei;

  stmt = (gimple) stmt_ptr;
  bb = gimple_bb (stmt);

  // A reexecution point must be a real instruction.
  if (gimple_code (stmt) == GIMPLE_PHI)
    stmt = gsi_stmt (gsi_start_bb (bb));

  if (stmt != last_stmt (bb))
    {
      gsi = gsi_for_stmt (stmt);
      gsi_next (&gsi);
      insert_setjmp_before (gsi);
    }
  else
    {
      FOR_EACH_EDGE (e, ei, bb->succs)
    {
      insert_setjmp_before (gsi_start_bb (e->dest));
    }
    }

  return true;
}


/* Verifies if a given STMT has non-idempotent side effects.  */

static bool
stmt_idempotent_destroying_p (gimple stmt)
{
  // Check calls.
  if (gimple_has_side_effects (stmt))
    return true;

  // Check for virtual definitions (wirte to heap, globals, aliased vars, etc).
  if (is_gimple_assign (stmt) && gimple_store_p (stmt))
    return true;

  // TODO: test this.
  if (stmt == reexec_counter_reset_stmt)
    return true;

  return false;
}


/* SSA properties garantee no static redefinitions. However, for phi functions
   that dominate the definition of at least one of its operands, copy insertion
   for SSA elimination may insert dynamic rewrites. Such rewrites may end up
   creating read-write sequences not preceded by another write instruction,
   which are idempotent-destroying. Such scenario only happens for phi
   functions in loop headers and affect idempotent regions that get passed the
   loop entry point. A stack checkpoint in the loop pre-header guarantees that
   such regions will always contain an actual write to every variable defined
   by a phi in the lop header. This will eventually lead to larger idempotent
   regions. Example:
                                                   |
          |         Reassignment after          __\|/____
       __\|/___     non-idempotent operation   | i0 = 0  |
      | i0 =0  |   '-----------,------------'  |  ...    |
      |  ...   |               |               | sys()   |
      | sys()  |               '-------------->| i3 = i0 |
      |________|                               |_________|
          |         ________                       |         ________
      ___\|/_______\|/___   |                  ___\|/_______\|/___   |
     | i1 = phi (i0, i2) |  |       --->      | i1 = phi (i3, i2) |  |
     |___________________|  |                 |___________________|  |
            |               |                        |               |
           ...              |                       ...              |
            |               |                        |               |
      _____\|/_____         |                  _____\|/_____         |
     | i2 = i1 + 1 |        |                 | i2 = i1 + 1 |        |
     |_____________|        |                 |_____________|        |
         |     |____________|                     |     |____________|
        \|/                                      \|/
*/

static void
insert_loop_header_checkpoint (basic_block header)
{
  gimple stmt;
  basic_block checkpoint_bb;
  edge e, entry_e;
  edge_iterator ei;
  imm_use_iterator ui;
  gimple_stmt_iterator gsi;
  struct pointer_set_t *seen_vars;
  vec<tree> vars_to_reassign;

  // The function entry block is a fake loop, so nothing needs to be restored.
  if (header->index == 0)
    return;

  if (bitmap_bit_p (headers_with_checkpoints, header->index))
    return;

  gcc_assert (header == header->loop_father->header);
  gcc_assert (header->loop_father->latch != NULL);

  seen_vars = pointer_set_create ();
  vars_to_reassign = vNULL;

  // The preheader will be used as checkpoint for the whole loop.
  if (EDGE_COUNT (header->preds) > 2)
    create_preheader (header->loop_father, 0);

  FOR_EACH_EDGE (e, ei, header->preds)
    {
  if (e->src != header->loop_father->latch)
    checkpoint_bb = e->src;
    }

  entry_e = single_succ_edge (checkpoint_bb);

  // Variables defined after all idempotent-destroying operations happen in the
  // pre-header do not need reassignment (do not bother looking at the phis).
  for (gsi = gsi_last_bb (checkpoint_bb); !gsi_end_p (gsi); gsi_prev (&gsi))
    {
      stmt = gsi_stmt (gsi);

      if (stmt_idempotent_destroying_p (stmt))
    break;

      if (is_gimple_assign (stmt))
    {
      tree lhs = gimple_assign_lhs (stmt);

      if (TREE_CODE (lhs) == SSA_NAME)
        pointer_set_insert (seen_vars, lhs);
    }
    }

  // Extract all phi operands that need reassignment, i.e, any operand defined
  // outside the loop before an idempotent-destroying operation.
  for (gsi = gsi_start_phis (header); !gsi_end_p (gsi); gsi_next (&gsi))
    {
      stmt = gsi_stmt (gsi);
      tree arg = PHI_ARG_DEF_FROM_EDGE (stmt, entry_e);

      if ((TREE_CODE (arg) == SSA_NAME)
          && !pointer_set_insert (seen_vars, arg))
        vars_to_reassign.safe_push (arg);
    }

  // Creates a reassignment for every conflicting variable in the checkpoint
  // block.
  while (vars_to_reassign.length () > 0)
    {
      gsi = gsi_last_bb (checkpoint_bb);
      tree old_var = vars_to_reassign.pop ();
      tree new_var = make_ssa_name (TREE_TYPE (old_var), NULL);
      gimple reassgn = gimple_build_assign (new_var, old_var);
      gsi_insert_after (&gsi, reassgn, GSI_SAME_STMT);

      FOR_EACH_IMM_USE_STMT (stmt, ui, old_var)
    {
      if ((gimple_bb (stmt))->index == header->index)
        {
          use_operand_p use_p;

          FOR_EACH_IMM_USE_ON_STMT (use_p, ui)
            SET_USE (use_p, new_var);
        }
    }
    }

  bitmap_set_bit (headers_with_checkpoints, header->index);

  vars_to_reassign.release ();
  pointer_set_destroy (seen_vars);
}


/* Register a new reexecution point and update the set of loops containing at
   least one reexecution point in their body.  */

static void
register_reexec_point (gimple stmt, bool update_loop_cuts)
{
  if (!pointer_set_insert (reexec_points, stmt) && update_loop_cuts)
    {
      struct loop *loop = (gimple_bb (stmt))->loop_father;
      bitmap_set_bit (cut_loops, loop->num);

      while ((loop = loop_outer (loop)) != NULL)
    {
      bitmap_set_bit (cut_loops, loop->num);
    }
    }
}


/* For every loop containing at least one reexecution point in its body, we
   insert reexecution points after uses of every variable defined by a phi
   function in the loop's header. We do that to avoid idempotent regions of
   code from becoming non-idempotent after copy insertion for phi elimination.
 */

static void
inspect_cut_loops ()
{
  struct loop *loop;
  unsigned int i;
  bitmap_iterator bi;
  gimple_stmt_iterator gsi;
  imm_use_iterator ui;
  gimple stmt;

  EXECUTE_IF_SET_IN_BITMAP (cut_loops, 0, i, bi)
    {
      loop = (*current_loops->larray)[i];

      for (gsi = gsi_start_phis (loop->header); !gsi_end_p (gsi); gsi_next (&gsi))
    {
      gimple phi = gsi_stmt (gsi);
      tree var = gimple_phi_result (phi);

      FOR_EACH_IMM_USE_STMT (stmt, ui, var)
        {
          struct loop * common_loop = find_common_loop(loop,
            (gimple_bb (stmt))->loop_father);

          // Test if the use is inside the current loop.
          if (common_loop->num == loop->num)
            register_reexec_point (stmt, false);
        }
    }
    }
}


/* Identify reexecution points as the starting points of the largest possible
   idempotent code regions before the statement pointed by GSI_IDEMP_END, in a
   backwards DFS fashion. Reexecution points are always located right after the
   locations reported by this function, in order to avoid handling cases in
   which the last instruction in a block is idempotent-destroying. Note that
   this function will eventually chage the CFG, in order to generate larger
   idempotent regions.  */

static void
extract_reexec_points (gimple_stmt_iterator gsi_idemp_end)
{
  basic_block idemp_end_bb;
  edge e;
  vec<basic_block> stack = vNULL;
  bitmap visited;
  bool start_at_idemp_end;

  visited = BITMAP_ALLOC (NULL);
  idemp_end_bb = gsi_bb (gsi_idemp_end);
  stack.safe_push (idemp_end_bb);
  bitmap_set_bit (visited, idemp_end_bb->index);
  start_at_idemp_end = true;

  // For simplicity, idempotent regions cannot end at a phi node.
  gcc_assert (gimple_code (gsi_stmt (gsi_idemp_end)) != GIMPLE_PHI);

  do
    {
      basic_block bb;
      gimple_stmt_iterator gsi;
      bool continue_search;

      bb = stack.pop ();
      continue_search = true;

      for (gsi = gsi_last_bb (bb); !gsi_end_p (gsi); gsi_prev (&gsi))
    {
      // In the first block, begin search right before the end of the idempotent
      // regions.
      if (start_at_idemp_end)
        {
          gsi = gsi_idemp_end;
          start_at_idemp_end = false;
          continue;
        }

      if (stmt_idempotent_destroying_p (gsi_stmt (gsi)))
        {
          continue_search = false;
          register_reexec_point (gsi_stmt (gsi), true);
          break;
        }
    }

      // Phi nodes can also destroy idempotency, as they may represent stores.
      if (continue_search)
    {
      for (gsi = gsi_last_phis (bb); !gsi_end_p (gsi); gsi_prev (&gsi))
        {
          if (stmt_idempotent_destroying_p (gsi_stmt (gsi)))
            {
              continue_search = false;
              register_reexec_point (gsi_stmt (gsi), true);
              break;
            }
        }
    }

      if (continue_search)
    {
      // Needed to restore dynamically reassigned variables.
      if (bb == bb->loop_father->header)
        insert_loop_header_checkpoint (bb);

      // Stop at counter reset if no other idempotent start point was found.
      if (bb->index == 0)
        register_reexec_point (reexec_counter_reset_stmt, true);
      else
        {
          edge_iterator ei;

          FOR_EACH_EDGE (e, ei, bb->preds)
            {
          if (bitmap_set_bit (visited, e->src->index))
            stack.safe_push (e->src);
            }
        }
    }
    }
  while (stack.length ());

  inspect_cut_loops ();

  BITMAP_FREE (visited);
  stack.release ();
}


/* Insert after GSI a conditional jump based on CMP_EXPR, expected to be false.
   The conditional is augmented with a branch prediction hint.  */

static void
insert_branch_expect_false (gimple_stmt_iterator* gsi, tree cmp_expr,
  basic_block true_bb, basic_block false_bb)
{
  tree cmp_val, cast_val, expect_ret;
  gimple cmp_stmt, cast_stmt, expect_call, cond;
  basic_block cond_bb;
  edge true_e, false_e;

  // Insert comparison expression.
  cmp_val = make_ssa_name (boolean_type_node, NULL);
  cmp_stmt = gimple_build_assign (cmp_val, cmp_expr);
  gsi_insert_after (gsi, cmp_stmt, GSI_NEW_STMT);

  // Insert brach prediction hint using "__builtin_expect".
  cast_val = make_ssa_name (long_integer_type_node, NULL);
  cast_stmt = gimple_build_assign_with_ops (NOP_EXPR, cast_val, cmp_val, NULL_TREE);
  gsi_insert_after (gsi, cast_stmt, GSI_NEW_STMT);
  expect_call = gimple_build_call (builtin_decl_explicit (BUILT_IN_EXPECT), 2, cast_val,
    build_int_cst (long_integer_type_node, 0));
  expect_ret = make_ssa_name (long_integer_type_node, NULL);
  gimple_call_set_lhs (expect_call, expect_ret);
  gsi_insert_after (gsi, expect_call, GSI_NEW_STMT);

  // Insert the actual branch.
  cond = gimple_build_cond (NE_EXPR, expect_ret,
    build_int_cst (long_integer_type_node, 0), NULL_TREE, NULL_TREE);
  gsi_insert_after (gsi, cond, GSI_NEW_STMT);
  cond_bb = gsi_bb (*gsi);
  true_e = find_edge (cond_bb, true_bb);
  false_e = find_edge (cond_bb, false_bb);

  if (!true_e)
    true_e = make_edge (cond_bb, true_bb, EDGE_TRUE_VALUE);

  if (!false_e)
    false_e = make_edge (cond_bb, false_bb, EDGE_FALSE_VALUE);

  true_e->flags &= ~EDGE_FALLTHRU;
  true_e->flags |= EDGE_TRUE_VALUE;
  false_e->flags &= ~EDGE_FALLTHRU;
  false_e->flags |= EDGE_FALSE_VALUE;
}


/* Instrument a failure site with thread rollback code, i.e., reexecution
   counter test and longjmp call. Example:

                                       |
                             _________\|/_________
                            | exec_c++            |
         |                  | if (exec_c < MAX_C) |          /|\
     ___\|/___              |_____________________|     ______|_______
    | abort() |    --->         |             |        | DISPATCHER() |
    |_________|               F |             | T      |______________|
         |                  ___\|/___    ____\|/____         /|\
        \|/                | abort() |  | longjmp() |         |
                           |_________|  |___________|         |
                                |             |               |
                               \|/            '---------------'
                                                abnormal flow
*/

static void
instrument_failure_site (gimple_stmt_iterator* failure_gsi)
{
  tree cmp_expr;
  gimple counter_inc, nop;
  gimple_stmt_iterator reexec_gsi, cond_gsi;
  basic_block failure_bb, cond_bb, reexec_bb;
  edge failure_e;

  // TODO: Test the number of reexecution times.
  // Insert reexecution counter increment.
  counter_inc = gimple_build_assign_with_ops (PLUS_EXPR, reexec_counter,
    reexec_counter, build_int_cst (unsigned_type_node, 1));
  gsi_insert_before (failure_gsi, counter_inc, GSI_SAME_STMT);

  // Create different blocks for the failure and reexecution sites.
  nop = gimple_build_nop (); // Split placeholder.
  gsi_insert_before (failure_gsi, nop, GSI_SAME_STMT);
  failure_e = split_block (gsi_bb (*failure_gsi), nop);
  failure_bb = failure_e->dest;
  *failure_gsi = gsi_start_bb (failure_bb);
  cond_bb = failure_e->src;
  cond_gsi = gsi_last_bb (cond_bb);
  gsi_remove (&cond_gsi, true); // Remove placeholder.
  cond_gsi = gsi_last_bb (cond_bb);
  reexec_bb = create_empty_bb (cond_bb);
  reexec_bb->loop_father = cond_bb->loop_father;

  // Insert the reexecution counter test.
  cmp_expr = build2 (GT_EXPR, boolean_type_node, reexec_counter, build_int_cst
    (unsigned_type_node, MAX_REEXEC_COUNT));
  insert_branch_expect_false (&cond_gsi, cmp_expr, failure_bb, reexec_bb);

  // Insert longjmp call in the reexecution block.
  reexec_gsi = gsi_start_bb (reexec_bb);
  tree buf_addr = build1 (ADDR_EXPR, build_pointer_type (ptr_type_node),
    j_buffer);
  gimple longjmp_call = gimple_build_call (builtin_decl_explicit
    (BUILT_IN_LONGJMP), 2, buf_addr, integer_one_node);
  gsi_insert_before (&reexec_gsi, longjmp_call, GSI_SAME_STMT);
  make_edge (reexec_bb, dispatcher_bb, EDGE_ABNORMAL);
}


/* Inserts an assertion before the dereference pointed by GSI in block BB to
   verify that ADDR_VAR holds a somewhat valid address. Example:

                                 |
        |                 ______\|/_______
     __\|/___            |      ...       |
    |   ...  |           | if (p == NULL) |
    | a = *p |           |________________|
    |   ...  |   --->        |      |_________
    |________|               |     T      ___\|/___
        |                  F |           | abort() |
       \|/                   |           |_________|
                             |    ____________|
                           _\|/_\|/_
                          |  a = *p |
                          |   ...   |
                          |_________|
                               |
                              \|/
*/

static void
insert_deref_assert (gimple_stmt_iterator *gsi, tree addr_var)
{
  tree cmp_expr;
  gimple fail_call, nop;
  gimple_stmt_iterator assert_gsi;
  basic_block cond_bb, assert_bb, deref_bb;
  edge e;

  // Create a new block for the assertion failure.
  nop = gimple_build_nop (); // Split placeholder.
  gsi_insert_before (gsi, nop, GSI_SAME_STMT);
  e = split_block (gsi_bb (*gsi), nop);
  deref_bb = e->dest;
  cond_bb = e->src;
  *gsi = gsi_last_bb (cond_bb);
  gsi_remove (gsi, true); // Remove placeholder.
  *gsi = gsi_last_bb (cond_bb);
  assert_bb = split_edge (e);
  e = single_succ_edge (cond_bb);

  // Insert the actual null pointer test.
  cmp_expr = build2 (EQ_EXPR, boolean_type_node, addr_var, null_pointer_node);
  insert_branch_expect_false (gsi, cmp_expr, assert_bb, deref_bb);

  // Insert the assertion failure exit (implemented as a trap).
  assert_gsi = gsi_start_bb (assert_bb);
  fail_call = gimple_build_call (builtin_decl_explicit (BUILT_IN_TRAP), 0);
  gsi_insert_before (&assert_gsi, fail_call, GSI_SAME_STMT);

  // TODO: Dump location info before assertion failure, to mimic actual
  // assert.h behavior.
}


/* Tranforms every other kind of failure point in assertion failures, so that
   they can be handled in the same way later.  */

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
      for (gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi))
    {
      stmt = gsi_stmt (gsi);

      // Verify if this is a pointer dereference (*p = a or a = *p).
      if (is_gimple_assign (stmt) && gimple_assign_single_p (stmt))
        {
          tree lhs, rhs, addr_var;
          enum tree_code lhs_code, rhs_code;

          lhs = gimple_assign_lhs (stmt);
          rhs = gimple_assign_rhs1 (stmt);
          lhs_code = TREE_CODE (lhs);
          rhs_code = TREE_CODE (rhs);

          if (TREE_CODE_CLASS (lhs_code) == tcc_reference)
            addr_var = TREE_OPERAND (lhs, 0);
          else if (TREE_CODE_CLASS (rhs_code) == tcc_reference)
            addr_var = TREE_OPERAND (rhs, 0);
          else
            continue;

          if ((TREE_CODE (addr_var) == SSA_NAME)
              && !pointer_set_insert (simplified_stmts, stmt))
            insert_deref_assert (&gsi, addr_var);
        }
    }
    }

  pointer_set_destroy (simplified_stmts);
}


/* Main entry point for concurrency bug recovery instrumentation.  */

static unsigned int
do_conair (void)
{
  basic_block bb;
  gimple_stmt_iterator gsi;
  gimple stmt;
  struct pointer_set_t *instrumented_asserts;

  // TODO: test if this function (simplification and instrumentation) works
  // when there is more than one assertion failure in the same block.

  // This pass requires loop info to work.
  gcc_assert (current_loops != NULL);

  sjlj_infra_initialized = false;
  reexec_points = pointer_set_create ();
  cut_loops = BITMAP_ALLOC (NULL);
  headers_with_checkpoints = BITMAP_ALLOC (NULL);
  instrumented_asserts = pointer_set_create ();

  // To keep idempotency at low level, no two variables can share the same stack
  // slot.
  flag_ira_share_spill_slots = FALSE;

  simplify_failure_sites ();

  // Indentify reexecution points and instrument failure sites.
  FOR_EACH_BB_FN (bb, cfun)
    {
      for (gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi))
    {
      tree fndecl;
      const char *posix_assert_fail = "__assert_fail";
      const char *bsd_assert_fail = "__assert_rtn";
      const char *self_assert_fail = "__builtin_trap";

      stmt = gsi_stmt (gsi);

      if (is_gimple_call (stmt)
          && (fndecl = gimple_call_fndecl (stmt)) != NULL_TREE)
        {
          bool is_assert_fail = (strncmp (IDENTIFIER_POINTER (DECL_NAME (fndecl)), posix_assert_fail, 13) == 0)
              || (strncmp (IDENTIFIER_POINTER (DECL_NAME (fndecl)), bsd_assert_fail, 12) == 0)
              || (strncmp (IDENTIFIER_POINTER (DECL_NAME (fndecl)), self_assert_fail, 14) == 0);

          if (is_assert_fail && !pointer_set_insert (instrumented_asserts, stmt))
        {
          prepare_sjlj_infra ();
          extract_reexec_points (gsi);
          instrument_failure_site (&gsi);
        }
        }
    }
    }

  pointer_set_traverse (reexec_points, instrument_reexec_point, NULL);

  // If setjmps were inserted, all effectful calls need edges to the dispatcher.
  if (sjlj_infra_initialized)
    link_effectful_calls ();

  pointer_set_destroy (instrumented_asserts);
  BITMAP_FREE (headers_with_checkpoints);
  BITMAP_FREE (cut_loops);
  pointer_set_destroy (reexec_points);

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
