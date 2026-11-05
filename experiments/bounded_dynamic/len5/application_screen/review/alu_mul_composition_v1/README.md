# ALU/MUL proof abstraction after certified word lemmas

No semantic soundness gap was found in the reviewed composition. This review ran
only Python structural comparisons in memory. It launched no synthesis or formal
query and changed no core, harness, or proof helper.

The exact certified decoder candidate is SHA256
`82a76125a33790027bf6b86cb97007d048759484d6e96027abd8fa9ad5d215db`.
The reviewed abstraction helper is SHA256
`f7f0cd1093bccefcaf86f45f9dbd65b7d9ff86964fedf4327ab26afd467b3349`.
`summary.json` records every source hash, the exact original cells and bit vectors,
all directly consuming muxes, and the structural checks. Small authoritative inputs
are snapshotted in `sources/`; the two large native core JSON files remain at their
hash-bound external paths. The existing decoder/domain certificates are prerequisites;
this audit does not replace their proofs or rerun their solvers.

| Cut | Unique original driver | Output bits | RTL origin |
| --- | --- | --- | --- |
| ALU result | `$procmux$11115`, `$pmux` | 145200–145263 | `rtl/expipe/exec-units/alu.sv:164–175` |
| MUL result | `$procmux$7848`, `$pmux` | 225756–225819 | `rtl/expipe/exec-units/mult.sv:80–115` |

Each entire 64-bit Y output becomes a fresh 64-bit `$anyseq` output using exactly
the same bit identities. Each output has one driver; neither intersects a primary
input, native state output, protected protocol alias, other cut, or certified
instruction-projection cell. All direct consumers use these values as full 64-bit
mux data inputs in `arith_rs.sv`; there is no sliced tag/control output cut.

The native candidate has 17,785 cells. All 17,783 cells outside the two substitutions
remain byte-for-byte identical, including all 1,232 native state cells and their
connections. Ports, aliases, module attributes, and every clock/reset/latency/tag
equation are retained. All 119 cells encoding the seven certified word-domain
assumptions remain identical. Applying the two cuts before or after adding those
encodings produces exactly the same JSON structure. The reviewed mode is
`alu_mul`; the optional branch-outcome cut is not used.

For any original trace under the declared reset and Harvard program platform,
the certified decoder substitution preserves behavior and all seven imported word
domains hold. Choose each fresh symbolic result equal to its removed driver's
original result at every cycle. Then every remaining native equation, state
transition, property, and imported lemma has its original value. Thus imposing
those already-proved lemmas on the abstraction still retains every original
constrained trace. A universal safety proof on this model transfers to the original;
an abstract counterexample can be spurious.

Retaining the handshake and latency equations does not mean arbitrary symbolic
payloads preserve the same control trace: later operands, addresses, branches, and
recovery can change. This is intentional overapproximation. No occupancy, readiness,
fairness, lifetime, branch, or instruction premise is added by the abstraction.

The combined query must first validate and import the exact native decoder and
word-domain certificates, retain a separate unabstracted hardware artifact, and
apply the cuts only to the proof model. Keep the original strict admission
assertion and preserve symbolic undefined/`anyseq` semantics through the JSON
formal frontend. Never physically map this model or credit its cuts as area savings.
At initial inspection the query CLI rejected decoder-plus-abstraction and the
existing ordering would have sent an abstracted design to the native-only lemma
importer; the parent was notified to integrate the new mode separately. This review
certifies the transformation composition, not a later query implementation.
