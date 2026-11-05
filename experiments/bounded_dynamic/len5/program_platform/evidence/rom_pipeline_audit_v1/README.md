# Harvard instruction recurrence audit

The root-owned `audit_program_rom.py` independently replayed the recorded Harvard
run against the text-only ROM. It matched all **983 active clock edges and 484
returned fetches**, including response valid, every payload bit, fault flag/code,
request grants, response readiness, cooldown, and flush-edge behavior. No
instruction recurrence mismatch was found. This is finite trace validation.

The retained selector and generated `AdmissionScreen.sv` use zero fault payloads.
Source review matches the actual platform lookup: alignment has priority over
mapping; 14 little-endian ELF words occupy addresses 0..52; unmapped and
misaligned requests return zero with codes 1 and 0, respectively; successful
requests use code 31. The pipeline captures zero/code31 when request-valid is
false, clears both instruction stages on a flush edge, and freezes both when
the core is not response-ready. Cooldown still updates on flush and does not
combinationally suppress responses. Runtime source uses `PIPE_NUM=2` and skips
both instruction and data answer registers; the data request stage plus two
pipeline stages give the observed three-cycle data service.

The audit helper's extra check that this run does not store into instruction
addresses also passes. This fact is not needed to make the new platform ROM
immutable: instruction and data storage are separate objects, independently
checked by the platform tests. It is not an internal assumption in the formal
query.

The instruction correspondence must not be extended into an unrestricted
data-memory equivalence claim. The formal harness supplies arbitrary data,
forbids data faults, and does not model sparse RAM contents or store/load
coherence. Actual sparse RAM can fault on other addresses; the qualification
only checks that this finite run has no data faults. Core load/store response
readiness is constant one in `load_buffer.sv:409` and `store_buffer.sv:428`.
Thus the active data pipeline timing agrees, and arbitrary return values admit
the recorded values. The formal data grant is `rst_ni`, whereas the native
skipped response stages pass the constant ready through even during reset;
there is no claim of identical reset-level interface grants.

`PROVENANCE.json` binds the exact source and frozen generated harness reviewed
here. Its normalization still invokes `prep` before making undefined constants
symbolic; that separate trusted-boundary concern was reported to the parent.
This package neither certifies a positive safety result nor accepts a hardware
optimization. The `formal_screen.py` snapshot is historical review evidence,
not an endorsement of that export/proof flow.

Reproduction command (output must be fresh):

```sh
python3 experiments/bounded_dynamic/len5/application_screen/audit_program_rom.py \
  --image /home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build/harvard_streaming_v1/instruction.hex \
  --vcd /home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build/harvard_streaming_v1/all.vcd \
  --output /tmp/harvard-rom-pipeline-audit.json --gap 2
```
