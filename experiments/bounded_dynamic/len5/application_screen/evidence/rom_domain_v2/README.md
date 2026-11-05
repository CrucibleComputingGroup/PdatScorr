# External instruction-domain closure

The actual frozen `AdmissionScreen.sv` Harvard instruction producer proves
`rst_ni && instr_rvalid_i -> instr_rdata_i in D` for all reachable cycles, where
`D` is the fourteen 32-bit words in the executable-only, 56-byte ROM plus zero.
The predicate includes fault responses and all 32 raw payload bits. It has no
exception, issue, retirement, or accepted-consumer qualification.

`summary.json` is the proof record. The positive SMT base check covers six steps;
temporal induction succeeds within that bound. Both stage invariants are proved
jointly with the external-response property. The only assumption is the original
`$initstate -> !rst_ni`; no stage invariant is added as a premise. The resulting
model has three assertions, one assumption, no covers, no initialized state bits,
and no remaining X/Z cell-connection constants. The native memory registers retain
their synchronous reset and unconstrained initial values. The property is disabled
while reset is asserted; the first reset edge establishes the stage invariants.
Later reset assertions and deassertions remain arbitrary.

The extraction removes the one core instance and changes all 23 core output ports
to independent arbitrary checker inputs. Thus addresses, requests, readiness,
flush, and their timing are unrestricted; no program-counter sequence is assumed.
It removes exactly the original three unrelated assertions (two data-readiness
obligations and one ALU admission bound). It adds only the observation aliases and
three properties. All remaining producer source is copied verbatim. The retained
two-stage pipeline still freezes on instruction-response backpressure, clears on
flush at the edge, and updates the fetch-gap counter by its original recurrence.
The unrelated data producer is retained in source and pruned from the output cone
by ordinary proof preparation. `positive/extraction.diff` exposes every change.

The safe generic frontend resolves undefined values to symbolic choices before
process lowering or optimization, and again after lowering. `prepare.ys`, complete
logs, small JSON/SMT models, the exact runner and backend snapshots, the source
summary, and the original full core port table are included. `core_port_descriptor_sha256`
binds the original large `core.json`; `core_ports_sha256` binds its packaged port
table. `SHA256SUMS` binds every packaged file except itself.

Two independently solved negative controls demonstrate an actual external-output
failure, with no helper assertions present:

| Changed producer | SMT step | Valid payload | Fault |
| --- | ---: | --- | ---: |
| Permit arbitrary payload on misaligned/unmapped instruction faults | 3 | `0x00000001` | 1 |
| Append `0xdeadbeef` at byte address 56, outside the original domain | 3 | `0xdeadbeef` | 0 |

Both models produce solver counterexamples and retained VCDs. The trace parser
requires a full payload sample and excludes SMTBMC's final clock/step-only marker.
The earlier v1 run proved the same positive result and found the same failures;
its report duplicated the final response into that terminal marker. The corrected
runner reran all proofs into fresh v2 directories. Historical v1 raw results and
its evidence package remain in the external build directory.

This result closes the reset-qualified external word premise of
`isa_baseline/results/program_alphabet_certificate_v3.json` for this exact generated
Harvard producer. Composing it with that separately source-bound decoder/data-path
certificate permits the proved native instruction-domain lemmas to be reused for
arbitrary unbounded core behavior. Applicability requires matching the generated
harness, ROM, original core port shape, reset convention, and all proof dependencies.
This result alone does not prove an ALU admission/occupancy bound, data-address or
data-fault restrictions, whole-core equivalence, or hardware savings.

Reproduce from the code repository, using the original frozen source directory and
fresh output directories:

```sh
python3 experiments/bounded_dynamic/len5/application_screen/rom_domain.py \
  --source /home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build/harvard_rom_decoder_symbolic_pdr_v1 \
  --output /tmp/harvard_external_domain_reproduction \
  --evidence /tmp/harvard_external_domain_reproduction_evidence
python3 -m pytest -q tests/unit/test_rom_domain.py
```

The default timeout is 60 seconds per tool call. All three proof preparations and
all four solver calls completed in less than a second each. The seven focused
tests pass: exact source extraction, rejection of unexpected assertions, assumptions
or port widths, both actual negative traces, and source/model/log hash bindings.
The runner omits JSON models from its compact evidence copy; their hashes are
always recorded, and this final review package additionally includes the three
small JSON models copied unchanged from the raw outputs.
