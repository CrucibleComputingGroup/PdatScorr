# Pscorr ISA/program-constrained baseline on fixed LEN5

These are Pscorr contributions: automatic native-logic specialization using ISA
or program facts, followed by conditional equivalence and ordinary synthesis.
The comparison needed next is **the same Pscorr baseline plus proved timing or
microarchitectural information**. No additional whole-core saving from timing
has been established here; that comparison is in
[ternary_reach](../ternary_reach/README.md). The ISA/program baseline is not presumed weak, and
the passes below are not an upper bound on program-only Pscorr.

| Fixed whole-core variant | Mapped cell area | Cells | Reduction |
|---|---:|---:|---:|
| Original LEN5 | 1,400,805.984001 | 160,447 | — |
| Pscorr ISA-operation decoder | 1,306,082.6368 | 145,581 | 6.7621% |
| Pscorr exact-word decoder | 1,300,886.4032 | 144,879 | 7.1330% |
| Pscorr exact-word decoder + architectural RF | 1,227,165.6992 | 136,304 | **12.3957%** |

All four use the same native JSON mapping flow, SKY130 HD typical library and
ABC settings. The older RTLIL-flow area 1,405,010.016 is **not** the denominator.
These are cell-area estimates, without layout, timing closure, power, or PPA
claims. No formal assumptions, assertions, or monitor state enter mapped RTL.
The original capacities and source parameters are unchanged: ROB32, IQ4,
ALU RS8, load buffer8, store buffer16, MUL/DIV/branch RS4, RAS8 and fetch FIFO2.

## What was discovered and proved

`prepare.py` extracts the exact original combinational issue decoder from LEN5
commit `14291dcc5bef181085d001c5a29e7f4fc4cbc8e9`. All 13 output ports are
observed. The original machine-mode privilege wiring is retained. `run.py`
enumerates both constants for each of 724 eligible scalar nodes; no particular
cell or constant is prescribed. The ISA domain permits LUI, ADDI, ADDIW, LD,
SD, BNE, SB and JAL with arbitrary register/immediate fields, plus zero. The
program-word domain contains the streaming kernel's 14 exact words, plus zero;
it does not constrain their order. The searches discover 641 and 642 constant
nodes respectively. Search results are proposals: a fresh combined, two-design
PDR proof of **all 13 decoder outputs** is required for acceptance.

`prove_domain.py` projects the original instruction data path while preserving
native data/reset transitions and combinational selectors. Other control state
is arbitrary, so this is an overapproximation. The only external premises are
initial `rst_ni == 0` and `(rst_ni && instr_rvalid_i) -> response word in domain`.
Invalid response payloads and all payloads during reset are unrestricted.
Per-word domain helpers are assertions, never assumptions. Six stored words
and the decoder input satisfy base plus induction. The closed-consumer audit
finds no external decoder consumer outside the 13 observed outputs. Together,
these proofs preserve all external core outputs and all state outside the
decoder, including ALU reservation-station state and its native aliases.

The architectural RF extension derives committed destination fields
`{0,5,8,9,10,11,18}` from the exact words, including fields of instructions that
do not write a register. A second original-data projection proves this set
through 40 native five-bit fields, including the ROB and commit path. It
assumes neither occupancy nor timing. A generic, unconditionally proved demux
expansion exposes all 32 write-address comparisons; it removes no arm. The
same exhaustive scalar search discovers 25 constant write decodes. Combined
sequential PDR proves both 64-bit RF read outputs equal for arbitrary read
addresses and write data under the derived destination domain and reset.
Those 128 bits cover every external native RF consumer. Ordinary cleanup can
then remove unreachable write/storage logic; no architectural or physical
register count is manually resized.

The final certificates are:

- [ISA decoder](results/isa_operations_certificate_v3.json)
- [Exact-word decoder](results/program_alphabet_certificate_v3.json)
- [Exact-word decoder plus RF](results/program_registers_certificate_v2.json)

All pair proofs use independent symbolic undefined choices before process
optimization and after sequential lowering. Native domain projections are
symbolized directly from JSON before optimization. The final RF domain also
symbols optimizer-generated undefined bits after sequential normalization and
checks that none remain. Decoder lower models contain no literal undefined
bits. Earlier unsafe frontend certificates are explicitly withdrawn; their
bytes remain under `results/withdrawn/`. Decoder v2 certificates used a stronger
reset-time external premise and are superseded by v3. The RF v1 certificate is
withdrawn and superseded by v2. None is a source of final acceptance.

## Interpretation and limits

The 12.40% result belongs to Pscorr using program facts. This experiment does
not compare against a competing optimizer or establish that ISA-only savings
are small. Pscorr can already prove microarchitectural facts from program-only
assumptions; the distinction is the information supplied, not the state that
the solver may reason about. Remaining strong controls include other
architectural operand/address restrictions, sequential correspondence/ODC
under program-only information, and exact instruction order or data facts.
Any timing-aware gain must be incremental to an appropriately strong matched
Pscorr baseline and use the same native hardware boundary.

The certificates are conditional on the stated external instruction domain.
The separately qualified Harvard platform returns only executable text words
or zero fault payloads, making this domain appropriate there. A unified ROM
containing data bytes does not automatically satisfy it. The word alphabet is
broader than the exact program: a concrete native counterexample already
disproves the proposed ALU-entry bound under arbitrary alphabet order. These
area results do not prove that bound or a timing-aware storage optimization.

## Reproduction

Run from the `BoundedDynamicPscorr` repository root. This is a workspace-relative
review package, not a standalone installed toolchain. It requires the pinned
frontend prepared by `experiments/bounded_dynamic/len5/prepare_frontend.py`, the
recorded Yosys/ABC/Z3 tools, SKY130 library, and kernel disassembly. The original
full data are retained at
`/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build`.
Use fresh output directories; scripts refuse to overwrite experiments.

```sh
P=experiments/bounded_dynamic/len5/isa_baseline
B=/absolute/path/to/fresh-isa-baseline
mkdir -p "$B"
python3 "$P/prepare.py" --output "$B/prepared"
python3 "$P/run.py" --prepared "$B/prepared" --domain isa_operations --output "$B/isa"
python3 "$P/run.py" --prepared "$B/prepared" --domain program_alphabet --output "$B/words"
python3 "$P/prove_domain.py" --prepared "$B/prepared" --domain isa_operations --output "$B/isa_domain"
python3 "$P/prove_domain.py" --prepared "$B/prepared" --domain program_alphabet --output "$B/word_domain"
python3 "$P/recheck.py" --candidate "$B/isa" --output "$B/isa_pair"
python3 "$P/recheck.py" --candidate "$B/words" --output "$B/word_pair"
python3 "$P/certify.py" --prepared "$B/prepared" --candidate "$B/isa" --domain-proof "$B/isa_domain" --pair-recheck "$B/isa_pair" --output "$B/isa_certificate.json"
python3 "$P/certify.py" --prepared "$B/prepared" --candidate "$B/words" --domain-proof "$B/word_domain" --pair-recheck "$B/word_pair" --output "$B/word_certificate.json"
python3 "$P/prove_domain.py" --prepared "$B/prepared" --domain program_alphabet --target-net u_backend.u_int_rf.comm_rd_idx_i --target-width 5 --instruction-field-low 7 --output "$B/rd_domain"
python3 "$P/prepare_registers.py" --prepared "$B/prepared" --base-candidate "$B/words" --decoder-certificate "$B/word_certificate.json" --domain-proof "$B/rd_domain" --output "$B/rf_prepared"
python3 "$P/prove_lowering.py" --original-rf "$B/rf_prepared/original_rf.json" --output "$B/lowering"
python3 "$P/run.py" --prepared "$B/rf_prepared" --domain program_alphabet --output "$B/registers"
python3 "$P/recheck.py" --candidate "$B/registers" --output "$B/register_pair"
python3 "$P/certify_registers.py" --decoder-certificate "$B/word_certificate.json" --original-rf "$B/rf_prepared/original_rf.json" --prepared-rf "$B/rf_prepared" --candidate "$B/registers" --domain-proof "$B/rd_domain" --pair-recheck "$B/register_pair" --lowering-proof "$B/lowering" --output "$B/register_certificate.json"
python3 "$P/map.py" --design "$B/prepared/whole_core.json" --output "$B/map_original"
python3 "$P/map.py" --design "$B/isa/candidate_whole_core.json" --output "$B/map_isa"
python3 "$P/map.py" --design "$B/words/candidate_whole_core.json" --output "$B/map_words"
python3 "$P/map.py" --design "$B/registers/candidate_whole_core.json" --output "$B/map_registers"
```

`collect.py` gathers the named final runs, checks raw hashes and binds their
native mapped inputs to certificates. It performs no simulation or synthesis:

```sh
python3 "$P/collect.py" --build-root /home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build --output "$P/evidence/final"
(cd "$P/evidence/final" && sha256sum -c SHA256SUMS)
```

The compact evidence omits full-core netlists, SMT/AIG models and bulk logs;
its manifest retains their original paths and hashes. Copied native-derived
component models retain LEN5 provenance and its upstream license notice.
