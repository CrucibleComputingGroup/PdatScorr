# Independent decoder certificate review

Reviewed `results/program_alphabet_certificate_v3.json` for importing the exact
native candidate JSON with SHA-256
`82a76125a33790027bf6b86cb97007d048759484d6e96027abd8fa9ad5d215db`.
No remaining must-fix gap was found for this conditional compositional import.
The audit script launches no synthesis or proof tool; it checks existing frozen
models, harnesses, scripts, hashes, and successful proof logs.

The fresh corrected-backend paired proof observes all 13 decoder output ports
unconditionally under the instruction-word premise. Its prepared model and AIG
retain 13 assertions and one assumption. Undefined values are made independently
symbolic before process optimization; no internal-state correspondence is
assumed for this combinational component. The proof succeeds with full PDR,
not merely a bounded check. Old constant-discovery results are not needed to
establish the final combined candidate's correctness.

The separate source-derived domain proof preserves six native instruction words
(two fetch spill fields and four issue-queue fields), 21 data-path cells, and 36
combinational control cells. Only 20 unrelated native control FF-Q bits become
arbitrary inputs. The retained controls preserve original spill-write gating
and selector relationships. The audit regenerated the projection from its
frozen method and original source; it exactly matches the proved input model.
The model has 194 symbolic undefined bits before `prep`, and no remaining x/z
cell connections before or after sequential normalization. Seven properties
(decoder word plus six stored words) pass both reset-base and induction. The
only two assumptions are initial reset and the external response-word premise.

Version 2 required `instr_rvalid_i -> word-domain` even during reset. That proof
was valid under its stated premise, but did not directly compose with arbitrary
initial outputs of the native **synchronously reset** memory pipeline. Version 3
closes this gap with `(rst_ni && instr_rvalid_i) -> word-domain`; reset-time and
invalid payloads remain unrestricted. The native instruction-bearing registers
have asynchronous reset to zero, so the stronger restriction was unnecessary.

The 642 changed cells are all combinational decoder cells. The component JSONs
used to export the proved pair match the corresponding original/candidate
whole-core cells exactly. All native state cells, non-decoder cells, top ports,
and net aliases remain unchanged. No modified cell overlaps retained domain
data or control logic. Every decoder-driven signal consumed outside the
component, including top outputs, is among the observed outputs: no consumer
leak was found. There are no formal monitors or added arbitrary inputs in the
native candidate.

These facts support unbounded compositional transfer of **all state and outputs
outside the decoder**, including ALU-RS state and its admission predicate, from
corresponding native initial states under initial reset and the stated external
word domain. The proof is not circular: the domain projection permits arbitrary
control-state values and is unchanged by the specialization; output equivalence
then preserves the surrounding transition relation at each step. The Harvard
ELF has exactly the same 14 words, and its defined fault payload is zero. After
the initial reset edge, its two-stage ROM pipeline can only hold/shift those
words or zero; the revised premise leaves its initial reset-time values free.

This is a compositional argument supported by the component and domain proofs,
not a standalone full-core equivalence-engine run. Import only the exact native
candidate JSON above; later optimized IL or other variants are not certified by
this review. The import does not establish an admission bound, a data-address
bound, or data-fault exclusion, and it is a program-only baseline simplification,
not evidence of a timing-constraint optimization gain.

`decoder_certificate_v3.json` records the independent checks and exact source /
proof hashes, including the SMT model, paired miter, candidate components, and
ELF manifest. Re-run `audit_decoder_v3.py` with the certificate path,
`--rom-manifest <elf_image_manifest.json>`, and `--output <new report.json>`.
`SHA256SUMS` covers this four-file review package.
