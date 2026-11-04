# RSD out-of-order specialization experiments

This directory is a review snapshot of authored scripts, source-derived formal wrappers/candidates, final measured summaries, selected small raw logs, and provenance. It preserves the original workspace-relative script layout and recorded paths; it is **not a standalone installed toolchain or a complete raw-data archive**. The original experiment guide is `WORKSPACE_README.md`.

The full original data remains at:

`/home/allenjin/Projects/DAC_pscorr/experiments/rsd_ooo`

Scripts were run there against pinned RSD `7b65f6ba0bce58d4d859082660123b7100aae975`. Reproduction requires that layout, the pinned RSD checkout, cross compiler, Verilator, and the formal/synthesis tools described by the retained guides/manifests. Absolute paths in copied results are intentionally unchanged. Most raw traces, binaries, toolchains, cloned RTL, huge mapping logs/netlists/AIG/SMT files, and obsolete exploratory families are omitted. Therefore the summary scripts that require raw traces cannot be rerun using this compact snapshot alone. Final summaries retain input, binary and trace hashes for comparison to the full dataset.

Review entry points:

- `paper-review.pdf`: compiled, blue-marked manuscript from the exact staged RSD revision; `PAPER_BUILD.json` records its source and PDF hashes. Concurrent DSL work is excluded from this review snapshot.

- `results/experiment_summary.json`, `results/application_summary.json`, and `results/latency_summary.json`: LSQ capacity, application and latency measurements.
- `results/scheduler_sweep/summary.json`, `results/prf_comparison.json`, `results/fp_scheduler/summary.json`, and `results/combined_region_scheduler/summary.json`: broader capacity controls and same-capacity candidates.
- `results/fp_memory/summary.json`: allowed FP-memory boundary checks.
- `formal/results/actual_lsq/summary.json`, `formal/results/scheduler_nofp/summary.json` and their proof logs: component proof evidence, not whole-core equivalence.
- `results/synthesis/*summary.json` and `*audit.json`: backend measures and source/provenance qualifications.

Results preserve limitations: ROB32 CoreMark bounded noncompletion remains in final evidence; FP and alias controls fail outside their contracts; PRF48 uses an explicit reset compatibility RTL change. Completed upstream CacheFlush/Fence tests can emit progress-watchdog diagnostics, and one unnamed assertion cannot be retrospectively identified. Finite trace matches and component proofs do not establish full-core/all-input equivalence. Observed occupancy peaks are not formal resource bounds.

Upstream-derived RSD candidate/compatibility sources are covered by `licenses/RSD_LICENSE`. CoreMark-derived interface material and RISC-V-test Dhrystone provenance are accompanied by their retained licenses; no general relicensing of third-party work is implied. The full vendored application sources remain in the original dataset and are fetched/prepared by the retained application builder.

`COPY_MANIFEST.json` maps every copied file to its original absolute path, byte count and SHA-256. `SHA256SUMS` covers all snapshot files except itself, including this README and the copy manifest. No experiment was rerun to create this snapshot.

## Repository ownership

This experiment code and evidence are maintained in `CrucibleComputingGroup/PdatScorr`. The manuscript is in [Allenjin123/DAC-2026-PSCORR](https://github.com/Allenjin123/DAC-2026-PSCORR). Keep bulk experiment artifacts out of that Overleaf-linked repository; its review folder links here.
