# Execution-unit domain diagnostic

The original native decoder satisfies `assigned_eu_o[2] == 0` under the existing
14-word program alphabet plus zero. Complete combinational SAT proves this
with all three native undefined choices symbolized before optimization.
Without the alphabet premise, SAT finds instruction `0x0200003b` (MULW), which
selects execution unit 4. The already certified program-word decoder candidate
satisfies the high-bit-zero property even with unrestricted instruction input;
safe combinational cleanup makes its high output bit a literal zero.

This rules out decoder undefined branches as the blocker for this particular
bit. Inspection of the retained safe whole-core model
`harvard_rom_decoder_symbolic_pdr_v1/screen.json` finds that the decoder high bit
is already zero, while the registered high bit and MUL/DIV issue-valid outputs
remain nonconstant. This is a sequential propagation gap, not another missing
combinational decoder cut.

The source and native signal path is:

1. `expipe_pkg.sv:220–230` assigns EU codes store=0, load=1, branch=2,
   ALU=3, multiply=4, divide=5. `issue_decoder.sv:83` defaults to ALU=3;
   multiply/divide assignments begin at lines 544/614.
2. `issue_stage.sv:293` feeds decoded `id_assigned_eu` into the issue register.
   Lines 312–320 implement asynchronous zero reset, zero on flush, and update
   on `ireg_en`. Native decoder bits are `[202158,202159,202160]`; the actual
   three-bit `$aldff` Q is `[91685,91686,91687]`, corresponding to packed issue
   register bits `[161:163]` in least-significant-first JSON order.
3. The high-bit D cone contains only three native mux slices. `$procmux$39601`
   selects old Q or decoded bit using native enable bit 91511.
   `$procmux$39604` has an undefined flush arm, but `$procmux$39608` overrides
   that arm with zero using the **same** flush bit 91658. Thus the undefined
   arm is masked; it is not an independent enable or a new premise.
4. `issue_stage.sv:351–353` initializes the valid vector to zero and sets the
   bit indexed by the registered EU. Native `$934` is the exact one-hot demux;
   the following native AND gates it with `cu_il_ex_valid`. MUL/DIV valid bits
   are 67868/71113 and feed `exec_stage.sv:221/251`.

In the safe formal model, the decoder high bit is literal zero, but
`async2sync` retains a three-bit internal FF and reset-output mux. The native
visible high-bit alias is 40380; internal FF bit 40377 is distinct. The native
visible alias is the appropriate target for a reset-based invariant. Assuming
that the internal transformed FF is zero at the initial frame would be
incorrect: it may initially be arbitrary while reset masks the visible output.

The physical mapping log performs enable extraction on the native issue
register. The proof preparation retains its history, and later combinational
cleanup cannot in general use a reset assumption embedded in formal
constraints to establish a state invariant. This explains the concrete
remaining selector path; it is not a complete attribution of the measured AIG
versus mapped-area difference across the whole core.

A cheap next step is to prove the exact native one-bit register projection,
including the three mux slices and original asynchronous reset, under
`decoded_high == 0` with arbitrary native enable/flush controls. Combined with
the existing decoder/input-domain proofs, that would establish the visible
registered high bit as zero. The original demux would then imply no MUL/DIV
issue. Removing or abstracting inactive units would still require their own
reset/state/output closure; no such removal is accepted here. The sequential
register theorem has **not** been run in this diagnostic.

Raw results are retained at
`/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build/eu_domain_diagnostic_v1`.
The compact [evidence package](evidence/eu_domain_diagnostic_v1/manifest.json)
contains source bindings, raw SAT results, the unrestricted counterexample,
native mux/FF/dispatch details and the inspected model hash. No final ISA
certificate, frozen importer, RTL capacity, or hardware implementation changed.

```sh
P=experiments/bounded_dynamic/len5/application_screen
B=/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build
python3 "$P/eu_domain_diagnostic.py" --prepared "$B/isa_baseline_prepare_v1" --candidate "$B/program_alphabet_v1" --frontend "$B/pre_fpu_frontend" --output "$B/eu_domain_diagnostic_fresh" --yosys /home/allenjin/Projects/DAC_pscorr/tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys
```
