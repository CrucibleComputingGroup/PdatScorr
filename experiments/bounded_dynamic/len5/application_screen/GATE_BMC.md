# Bounded diagnostic of the saved GLA abstraction

One 128-frame search on the saved **491-FF, 9,650-AND** abstraction found a
counterexample at **frame 25**, in 8.05 seconds wall time (ABC reports 7.89
seconds). ABC `testcex` validated the saved trace against that exact AIG. This
is an **abstraction-only counterexample**. It shows why this abstract model
cannot yield a safety proof; it does not establish a violation in the original
proof model or native core.

`gate_bmc.py` calls the existing strict `validate_prepared` and transitive
word/ROM dependency checks before and after the query. It checks all saved GLA
artifact hashes and calls the frozen `gate_pdr.rederive_map` to reproduce the
recorded AIG exactly from its saved map. The target command reads the already
folded one-output AIG directly and runs `bmc3 -F 128 -T 120 -v`. It adds no
assumptions and performs no folding or refinement. The validation command
reads the same AIG and saved status, then runs `testcex` before exporting the
witness. The AIG SHA-256 is
`d9544bac5ccd5b9a4e447704ec0577a2d62243ecf9ee0b1d94d4d991cf8e325f`.

Two tiny real-engine controls establish an eight-frame bounded pass and a
validated frame-1 counterexample. Six additional parser controls reject
partial bounds, timeouts, command failures, and contradictory statuses: all
eight tests pass. The pinned ABC prints `Resource limit reached (conf limit 0)`
even on ordinary `-F` completion; the parser recognizes that disabled-limit
footer while rejecting actual timeout/conflict-limit termination. A bounded
pass is always labeled `bounded_only_no_certificate`, never a proof.

[Compact evidence](evidence/gate_bmc_v1/PROVENANCE.json) contains 45 files,
306,764 bytes: the exact derived AIG, replay commands/logs, target status/logs,
validated witness, both toy models/results, source snapshots, and hashes.
The larger unchanged source map is already packaged under
`evidence/gate_solver_v1/query/final_map.aig.gz`; its hash is bound in the new
provenance. Raw results remain at
`/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build/harvard_rom_word_lemmas_alu_mul_gla_bmc128_v1`.
No further target search or refinement is part of this frozen result.

Reproduce using a fresh output directory:

```sh
BUILD=/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build
APP=experiments/bounded_dynamic/len5/application_screen
python3 -m pytest -q tests/unit/test_gate_bmc.py
python3 "$APP/gate_bmc.py" \
  --gla-result "$BUILD/harvard_rom_word_lemmas_alu_mul_gla_v1" \
  --output "$BUILD/gla_bmc128_reproduce" --frames 128 --timeout 120
```

The original prepared query already contains ALU/multiplier abstractions.
Even a future counterexample concretized through this GLA map would belong to
that proof model until checked against native RTL. Native hardware is unchanged;
this diagnostic accepts no optimization and makes no physical saving claim.
