# Independent native GLA wrapper review

No blocker was found in the frozen `native_gate_solver.py`. The wrapper accepts only the reviewed native-arithmetic query, exact `inactive_query_core.json`, immutable zero-fault ROM, closed decoder/word/ROM/inactive facts, and the original three assertions/eight assumptions. It requires 1761 reset substitutions with no new premise or hardware-export change.

All 269 theorem dependencies are validated before and after the engine call, including their inclusion in the existing word-import dependency map. The prepared summary is hash-bound across the call, and the wrapper, shared gate engine, and prepared-model validator are also snapshotted and checked. The input AIG remains bound to the preparation.

The wrapper invokes the same qualified `gate_solver.run_gla` function without changing its command sequence or model. Constraints are folded before ORing all bad outputs and converting to GIA. Only an explicit unbounded terminal result together with the matching UNSAT status can pass; a concrete-counterexample result requires separate `testcex` validation against the original folded query. Timeout, abstraction stability, and bounded progress remain inconclusive. The wrapper caps its requested budget at 600 seconds.

Ten wrapper tests passed in 0.49 seconds. Their engine calls are mocked; the real prepared-query dependency validator is exercised. Four additional verdict-parser checks passed. This reviewer launched no target or toy solver. The separately authorized running GLA outcome is outside this report.
