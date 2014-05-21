# ConAir for GCC

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
