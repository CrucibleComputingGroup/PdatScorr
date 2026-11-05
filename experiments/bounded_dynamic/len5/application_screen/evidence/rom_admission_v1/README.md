# Address-indexed ROM admission screens

Both screens retain the original native arithmetic and all declared capacities.
They assert that ALU admission never selects indices0–3; they do not assume it.
Instruction addresses come from the core, with no assumed PC sequence. Data
responses remain symbolic, nonfaulting, and three cycles after accepted requests.
This data-service premise is not yet proved for every future sparse-RAM access.

The first run uses the old entire4736-byte unified image as immutable instruction
ROM, including data bytes, with arbitrary payload on instruction faults. ABC
reports no counterexample in25frames but hits its120s limit before the requested
64frames. Its historical `bounded_only_no_certificate` status does not mean a
completed64-frame check.

The second uses the ELF executable-only56-byte Harvard ROM with zero instruction
fault payload. PDR returns unknown after120seconds. Neither run accepts an
optimization or establishes a storage-removal bound.

Both historical preparation scripts run `prep` before explicit undefined-value
symbolization. That ordering is under correction. These results are preserved
as inconclusive experiments, never positive certificates. Raw bulk source JSON,
Verilog, and AIG remain in the external build directories referenced by summaries;
their hashes are recorded. This package retains exact harnesses, source snapshots,
images, commands and logs. `SHA256SUMS` binds every packaged payload.
