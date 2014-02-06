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
#include "stor-layout.h"
#include "flags.h"
#include "tm_p.h"
#include "basic-block.h"
#include "function.h"
#include "gimple-pretty-print.h"
#include "hash-table.h"
#include "tree-ssa-alias.h"
#include "internal-fn.h"
#include "gimple-fold.h"
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
#include "tree-ssa-propagate.h"
#include "value-prof.h"
#include "langhooks.h"
#include "target.h"
#include "diagnostic-core.h"
#include "dbgcnt.h"
#include "params.h"


/* Main entry point for concurrency bug recovery instrumentation.  */

static unsigned int
do_conair (void)
{
  // TODO: Pass code.

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
