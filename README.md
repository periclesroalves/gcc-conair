# ConAir for GCC in a Nutshell

<p style='text-align: justify;'>Concurrent programming is a notably hard task.
Even though developers often have a number of tools in hand to help them avoid
concurrency bugs during development, managing concurrent resource access,
particularly for large code bases, is still highly error-prone. Thus, it comes
as no surprise that even industrial quality software often contain a number of
hidden concurrency bugs after deployment. Such bugs when exposed to the end user
usually end up in severe failures. Even when developers are notified of a
failure in deployed software, fixing concurrency bugs may still be harder than
avoiding them, as their causes are usually hard to identify. This scenario
exposes the need for a technique capable of making computer programs able to
recover from concurrency failures in an automated way.</p>

<p style='text-align: justify;'>ConAir [link to paper] is a tool designed to
instrument existing source-code with concurrency bug recovery and survival
capabilities. It does so by means of re-execution of idempotent [link to
idempotency] code. Right before the program reaches a failure state that is
caused by the inconsistency of resources shared with other threads, i.e., global
variables and acquired resources, ConAir rolls back the thread being executed.
By doing that a number of times, re-executing a region of idempotent code, we
hope that the state exposed by other threads becomes consistent. When that
happens, execution is resumed and the failure state is no longer reached, thus
recovering from a concurrency bug.</p>

<p style='text-align: justify;'>In this article we describe the implementation
of ConAir in GCC, the GNU Compiler Collection. Our main goal here is to provide
a development overview and expose the technical challenges of implementing this
tool in an industrial-strength compiler. For a detailed explanation of the
theory behind the tool and its underlying algorithms, please refer to the main
ConAir paper [link to paper].</p>

The technique behind ConAir is divided into three main steps, whose implementation is explained in the following sections of this text:

  - Failure site identification.
    - Assertion failures and assert functions.
      - {__assert_rtn and __assert_fail}.
    - Instrumenting pointer dereferences.
      - {__builtin_trap}.
  - Re-execution point identification.
    - Defining idempotent code.
      - {traditional idempotent-destroying operations}.
      - {explain backwards DFS}.
    - Idempotency on the GCC SSA representation.
      - {real and virtual operands}.
      - {link to GCC summit SSA paper}.
      - {stack and register sharing}.
    - Dynamic reassignments and loop checkpoints.
      - {link to Marc's paper}.
  - Rollback instrumentation.
    - The choice for setjmp/longjmp.
      - {register restoring properties}.
      - {Avoid code motion into idempotent regions}.
    - GCC built-in setjmp/longjmp.
      - {reuse of non-local goto machinery}.
      - {the need for a dispatcher blocks and abnormal edges}.
      - {the need for a proxy function}.
      - {linking effectful calls: effectful functions may contain longjmps to
        the function that calls them, so every effectful call needs an abnormal
        edge to a dispatcher block.}.
      - {Why do we need different dispatcher blocks for different failure points
        and its respective reexecution points}.
        - {For sjljs inserted by hands, GCC links all of them to a single
          dispatcher block, even if the reference different jump buffers}.
        - {How a single dispatcher can break the SSA form if inserted during
          compilation: a single dispatcher
          may lead to uses not dominated by a definition [give example]. In fact
          we know that definitions will never be skipped, because setjmps need
          to be called a first time in order to be reachable, but that can't be
          represented in SSA form with a single dispatcher}.
        - {Solution: the obvious solution would be to insert phis for all
          problematic definitions. Hoever, it was complicated to get GCC's ssa
          fix pass to do that automatically. Seen that, we proposed an
          instrumentation strategy that links different failure points to
          different dispatcher blocks, thus solving the problem:}
            - {For failure points not in loops: identify reexecution points as
              usual}.
            - {For failure points in loops: simply insert a reexecution point
              right before the failure site (idempotent region size equals
              zero). This eliminates the need for a checkpoint (though we will
              leave it in the code by now) and inserting
              cuts after every read of dynamically reassigned variables in the
              loop. We could extend the idempotent regions to the loop entry
              with no problem, but then we would have to figure out to which
              dispatcher the cuts after problematic reads should be linked to}.
            - {Algorithm description:
                . Every longjmp is linked to a different dispathcer block.
                . All setjmps related to a given longjmp are linked to the same
                block.
                . in case a setjmp is related to more than one longjmp, the
                setjmp is linked to the dispatcher blocks of the two longjmps.
                . All effectful calls are linked to a specific dispatcher block,
                which is linked to the setjmp on the function entry.
              }


## TODO List

### TODO - correctness
- Update loop info for all blocks created in *insert_deref_assert()*.
- When looking for assertion failures in the code, we need to figure out how to verify if the **assertion function** being called was really loaded from the standard library or if it was redefined by the user. The current implementation just performs textual comparison of the function name.

### TODO - performance
- GCC has two kinds of **profile feedback**: an on-line version, which requires a test run, and an off-line version, based completely on statistical methods and heuristics. Both versions depend on **frequency counters/factors** associated with basic blocks and edges. We need to learn how to update these counters properly, as this may have direct impact on performance.
- When handling **dynamic reassignments** we insert a reexecution point after every read of a conflicting variable. This ends up inserting a lot of redundant reexecution points. We only need to guarantee that no read reaches a failure site without crossing at least one reexecution point. Seen that, an instance of the **taint flow analysis** algorithm could be used to eliminate redundance.
- In the presence of setjmps, GCC requires an **abnormal flow edge** from every effectful function call to a dispatcher block. We can probably avoid this due to the fact that we have full information about which functions can make abnormal gotos.

### Improvements
- The pass needs to be textually documented in *trunk/gcc/doc/*.
- If we implement any kind of inter-procedural analysis, the **jump buffer** and **reexecution counter** declarations must be changed to thread scope. Currently this declarations are local to the function, which is fine because different threads have different call stacks. (NOTE: it seems quite complicated to create new thread variables at this point, due to how GCC emulates **thread local storage**)
- Many **built-in functions** already are or need small changes to be idempotent preserving. Verifying this when checking function side-effects could increase considerably the lenght of reexecution regions.
- Currently we only instrument **pointer dereferences** against null values. In addition to that, we can verify if the address being dereferenced is within the program segment (protecting against things like address miscalculation).
- Improve our **graph-consistency checking** pass: currently it only checks instrumented pointer dereferences.
- We need to heuristically define the threshold for the **reexecution counter**.
