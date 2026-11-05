# Original native-core ROM query, symbolic undefined values

The corrected formal preparation preserves undefined choices before optimization
and after lowering. The actual executable-only Harvard instruction ROM returns
zero on fetch faults, with native two-stage fetch and three-stage data timing.
All native capacities and arithmetic remain unchanged. No ISA-specialized model
or certificate is used in this query. It asks whether ALU admission can ever
select entries0–3; that fact is asserted, not assumed.

PDR returns **unknown after120seconds**. No storage rewrite or area saving is
accepted. The external data service is nonfaulting with arbitrary returned load
values; this is a declared formal domain and not a universal proof that all
future accesses in the sparse-RAM simulation stay mapped. Synchronous memory
pipeline reset is retained, with initial core reset required.

Exact source snapshots, harness, image, commands and PDR log are archived here.
Bulk native JSON/Verilog/AIG remain at the external build paths and are hash-bound
by the summary. The earlier normalization-limited experiments remain separately
archived in `../rom_admission_v1`.
