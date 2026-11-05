# GLA on the combined native-arithmetic query

The single 600-second diagnostic ended **unknown**, with an explicit GLA timeout
in frame 29 and zero stable frames. Its wall time was 601.159 seconds; the raw
status is `snl_UNK 28 unknown`. There was no unbounded proof or validated target
counterexample. No concurrent proof-thread calls occurred. The last saved map
derives to 629 latches, 13,106 AND nodes and 1,508 inputs; those sizes are not
hardware savings or a certificate. All post-run dependency checks passed.

`combined_gate_solver.py` is a separate entry point for the closed reset-cube
query with three safety assertions and 48 assumptions. It reuses the unchanged
qualified `gate_solver.run_gla` implementation. The native hardware export,
exact Harvard ROM and native arithmetic are preserved; this diagnostic adds
no premise or payload abstraction and generates no hardware candidate.

Before its one target call, the wrapper validates the complete preparation and
all 2,329 transitive proof dependencies. It also runs a real installed-tool
qualification: 48 independent input constraints make a sequential OR property
safe; omitting only the final constraint produces a counterexample validated
against the original folded toy model. The toy keeps the data register's
arbitrary initial state and begins observation after its first update.

The target path folds all AIGER constraints, ORs the three bad outputs, and
passes the resulting one-output model to `&gla -q -T 600 -v -m`. Only the
existing strict unbounded-proof parser can certify this safety query. A SAT
verdict must pass `testcex` on the original folded combined query. A smaller
map, stable abstraction, bounded success or timeout is inconclusive. Saved
maps are proof-only overapproximations. No PDR or continuation is started
automatically.

The wrapper checks the complete model/proof closure, helper snapshots and
ABC/Yosys executable hashes before and after the run. The immutable prepared
input is `build/harvard_rom_register_status_cube_native_prepare_v1`; the raw
diagnostic output is `build/harvard_rom_register_status_cube_native_gla_v1`.
The target engine files live in its `gla/` directory; the qualification is in
`qualification/`. The top-level summary records both and their bindings.

The compact package is `evidence/combined_gate_solver_v1`: 70 files and
5,189,488 bytes, including the compressed maps, complete logs, qualification
witness, source snapshots and proof bindings. All 69 manifest entries verify.

Ten wrapper tests pass, including rejection of changed premises, abstraction,
fault payload, query path and transitive proof files; a post-run mutation test;
the real 48/47-constraint pair; and the actual prepared dependency closure.
Together with the existing engine verdict/initial-state regressions, the
focused suite has 20 passing tests.

To reproduce after restoring the recorded preparation and its closed proof
dependencies, choose a fresh output directory:

```sh
python experiments/bounded_dynamic/len5/application_screen/combined_gate_solver.py \
  --prepared /path/to/harvard_rom_register_status_cube_native_prepare_v1 \
  --output /path/to/fresh-combined-gla \
  --timeout 600
```

Package a terminal run without rerunning a solver:

```sh
python experiments/bounded_dynamic/len5/application_screen/collect_combined_gate.py \
  --query /path/to/fresh-combined-gla \
  --source-audit /path/to/gate_solver_source_analysis_v1 \
  --output /tmp/len5-combined-gla-evidence
```

The installed ABC binary remains source-audited with a version caveat: its
exact correspondence to the accessible source checkout is unestablished.
The existing installed-symbol/disassembly audit and real positive/negative
qualifications support the command-flow interpretation; this diagnostic does
not infer an unbounded result from source inspection alone.
