# Refinement interface probe: target not launched

The [validated frame-25 abstraction counterexample](GATE_BMC.md) remains
**abstraction-only**. The installed ABC `&gla_refine` interface did not pass
the tiny plumbing controls required before attempting target refinement.
No target refinement or additional safety search was launched.

The diagnostic reused two previously qualified tiny gate maps and their
validated abstraction counterexamples. Each map was rederived and compared
byte-for-byte with the recorded abstraction; `testcex` checked the input trace
against that exact AIG. The command then read the saved original map and
saved CEX status and invoked `&gla_refine -F 0 -G 0 -v`.

| Tiny original | Observed refinement behavior | Returned status/witness |
|---|---|---|
| Independently proved safe; coarse-map CEX is spurious | Validates input CEX, refines through two frames | `snl_UNK`, `NULL` |
| Independently validated original counterexample | Validates input CEX and logs a true counterexample at frame 1 | `snl_UNK`, `NULL` |

The second case additionally prints that structural hashing invalidated the
mapping while reading it. The strict probe rejects that warning and exits
with `ValueError`; it does not treat an internal “true counter-example” log
as a validated concrete result. The target saved map did not print this warning
in its earlier exact derivation replay, but the lost concrete status/witness
still prevents the requested reliable concretization interface.

The local ABC source explains the lost result. `Abc_CommandAbc9GlaRefine` calls
`Gia_ManNewRefine`. That function checks the supplied trace against the derived
abstraction and invokes bounded GLA on a temporary transformed manager. It
then destroys that manager without transferring its concrete CEX, and always
returns `-1`. The caller receives unknown status and no concrete trace to
validate. The older `Gia_ManGlaRefine` implementation can remap a concrete CEX,
but it has no call site in this checked source tree; the installed command
uses the newer function. No tool changes or alternate interfaces were tried.

The clean local source commit is
`5d51a5e420f5de493d07bf61109a977248c86ffb`. Source inspection agrees with the
observed installed-binary behavior; the source checkout is not represented as
independent proof of binary build provenance. Relevant source, license,
binary/source hashes, commands, raw statuses/logs, and toy inputs are preserved
in [the 29-file diagnostic package](evidence/refinement_probe_v1/PROVENANCE.json)
(111,372 bytes). The old target preparation and transitive dependencies were
revalidated unchanged after this probe.

`refine_map_probe.py` reproduces the failed-closed controls using fresh output
directories; `collect_refine_probe.py` packages the recorded result without
running any tool. A successful reproduction is expected to stop at the
binding warning, not return a qualified target verdict. Full raw artifacts:
`/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build/gate_refinement_probe_v1`.

Even a future validated CEX on the original saved query would still belong to
its proof model, which includes ALU/multiplier abstractions, until checked
against native RTL. This diagnostic accepts no optimization or hardware claim.
