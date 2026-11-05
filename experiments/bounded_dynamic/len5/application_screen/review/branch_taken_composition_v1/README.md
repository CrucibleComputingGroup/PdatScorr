# Branch-outcome abstraction addendum

The existing `alu_mul_branch_taken` mode is a sound proof-only overapproximation
after the same certified decoder substitution and seven proved native word lemmas.
This review uses only in-memory structural comparisons and a read of the pinned
upstream RTL. No new backend query or assumption was introduced.

The third cut is exactly bit **46726**, alias
`u_backend.u_exec_stage.u_branch_unit.res_taken`, driven solely by the complete
one-bit Y port of `$procmux$20161` (`$pmux`). The pinned source is
`rtl/expipe/exec-units/branch_unit.sv:111–123`: comparisons for conditional branches,
constant one for jumps/calls/returns, and a default zero. The replacement is one
fresh `$anyseq` bit. No state, input, tag, clock, or reset bit is cut.

Its direct consumers implement the taken/misprediction comparison at line 157,
the target-alignment exception condition at line 165, and branch-result selection
at lines 196–203. Arbitrary outcomes deliberately relax those behaviors, including
allowing a not-taken unconditional jump. This may create spurious counterexamples;
retaining the native control equations does not preserve their values on arbitrary
abstract traces.

All **1,232 native state cells**, all native ports/aliases, and all **119 cells
encoding seven lemma assumptions** remain identical. Only the three named drivers
change: 17,782 other native cells remain identical. The third cut has no overlap
with native instruction-projection cells or inputs, or with lemma encodings.
Adding the lemmas and applying the cuts commute exactly in this model. The mode
introduces **129 fresh symbolic bits per cycle** in total.

Every original constrained trace remains included: select the original ALU result,
MUL result, and actual branch outcome at each step. Then all retained equations,
state transitions, and already-proved lemmas retain their original values.
Consequently a universal safety proof transfers to the original model. More
generally, projection overlap would not itself break this trace-inclusion argument
when the lemmas were established on the original first; it would prevent claiming
that the abstract projection's equations were unchanged. No such overlap occurs
here.

`summary.json` binds the exact candidate, helpers, certificates, domain projection,
prior two-cut review, native branch source, and every third-cut connection. The
previous review retains small source snapshots; this addendum retains the reviewed
abstraction helper and branch RTL. This result is neither an admission proof nor
a hardware/area result. The subsequent generated query remains separately auditable.
