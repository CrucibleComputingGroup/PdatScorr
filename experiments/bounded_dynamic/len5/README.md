# LEN5 frontend qualification and timing-candidate review

This directory qualifies a smaller genuine out-of-order target for automatic
Pscorr optimization under timing contracts. Qualification is separate from the
subsequent [storage inventory and screened plan](STORAGE_SAVINGS_PLAN.md),
[unchanged-core mapped baseline](results/native_area_v1/summary.json), and
[DIV occupancy counterexample](results/div_falsifier_v1/summary.json).
These results establish no timing-derived storage saving or queue-resizing gain.
The timing ablation itself is in [ternary_reach](ternary_reach/README.md). There,
Pscorr given LEN5's fixed native timing removes at least 18,408.9 µm² (1.31% of
the original core) beyond its program-only bound, with capacities and runtime
unchanged.

**Qualification passed:** unchanged pre-FPU RTL elaborates, normalized structural
checks pass, and a self-checking smoke passes with an actual tagged memory
response and a recorded example of out-of-order ALU selection. Compact evidence
is in [results/qualification.json](results/qualification.json).

## Qualified source and fixed baseline

Use the official pre-FPU revision
[`14291dcc5bef181085d001c5a29e7f4fc4cbc8e9`](https://github.com/edge-group-polito/len5/tree/14291dcc5bef181085d001c5a29e7f4fc4cbc8e9)
(2024-05-08), the first parent of the upstream FPU merge
`5206e92bc7235cd1cbcc10522aaee3f69f9b5e7b` (2025-10-22).
Its **74 selected RTL files are unchanged**, including the original configuration:
`LEN5_FP_EN=0`, integer multiply/divide enabled, and store/load forwarding enabled.
No configuration switch, queue capacity, or functional RTL repair is applied.
The clean detached checkout remains at `5206e92` in the workspace's external
`experiments/bounded_dynamic/deps/len5`; the preparation
script reads the older git objects into a separate generated snapshot.

The repository's root license is Solderpad Hardware License 2.0;
vendored components retain their own notices. Several `.core` headers separately
identify SHL 2.1; preserve each source's license rather than normalizing them.

The capacities are the same in both upstream revisions:
ROB32, predispatch IQ4, LB8, SB16, ALU RS8, MUL/DIV/branch RS4, RAS8. The
`datapath` top keeps its default instruction-interface FIFO depth 2 and boot PC0.

## Reproduction

Requirements for the explicit frontend path: Python3, PyYAML, and a Yosys build
with the slang plugin. The default uses the existing workspace OSS CAD Suite
2026-11-04. The 74-file source list follows the upstream `.core` manifests.
No FuseSoC or network access is needed
after checkout, and `hierarchy -check` rejects unresolved active modules.
The scripts live in the Pscorr code worktree. They locate the enclosing workspace's
`tools/oss-cad-suite-20261104` directory and keep bulky builds and the source clone
outside the code repository. Explicit `--deps`, `--build`, `--frontend`, and
`--yosys` paths are available when using another workspace layout.

For a fresh source checkout, clone `https://github.com/edge-group-polito/len5`
without `--depth`, then detach it at `5206e92bc7235cd1cbcc10522aaee3f69f9b5e7b`.
The scripts verify that checkout's pin and cleanliness, and read the official
pre-FPU commit directly from its git object database.

```sh
python3 experiments/bounded_dynamic/len5/prepare_frontend.py --profile pre_fpu
```

Use `--yosys PATH`, `--deps PATH`, or `--build PATH` when needed. Generated
sources, exact script, file list, RTLIL, and logs go under ignored
`build/pre_fpu_frontend/`. `--prepare-only` emits the inputs without elaborating.
The raw structural check reports one duplicate constant-zero driver of the LB
`mem_we_o` output. Standard `opt_expr; opt_clean` resolves the identical aliases;
the subsequent `check -assert` reports **zero problems**. The raw failure and
the successful normalized check are both retained. No RTL line is removed.
There are three frontend warnings for missing reset values in RAS and branch-confirm
fields; this frontend check is not a hardware-correctness proof.

Simulation qualification uses the upstream bare testbench and C++ driver without
FuseSoC. It needs Verilator, host C++, and an RV64 compiler/objcopy; the smoke is
freestanding assembly, so it does not require newlib or the upstream application
runtime. The script selects host binutils before the inherited workspace PATH.

Only the external testbench is adapted: two erroneously `const` variables that
are assigned by methods become mutable, and its fetch FIFO setting is fixed to 2
to match the unmodified core default. A trace helper's ROB index is assigned on
every call instead of once through static initialization. A read-only event
monitor records actual ROB dispatch, ALU execution/result handshakes and load
requests/responses. These changes drive no core state or handshakes.
The external memory model uses `PIPE_NUM=2`; this is a model setting, not a core
capacity change or an assertion that every request has exactly two cycles of
latency. The observed smoke's load response arrives three monitor cycles after
acceptance. Instruction responses bypass their final answer register in the
original testbench: their unstalled latency is two cycles, with longer intervals
under backpressure. The separate [instruction-spacing screen](application_screen/FETCH_SPACING.md)
measures actual accepted fetches, flush cancellations, response handshakes, and
load exceptions while preserving FIFO2 and all core capacities.
The build/run manifests bind all core and testbench
hashes and commands. The smoke checks an integer loop and a store/load result;
it also checks a preinitialized load and a dependent ADDI. It does not qualify
the full ISA.
Upstream C++ returns zero even after timeout or nonzero program exit, so the
wrapper checks the actual success message and nonempty commit trace as well.
It rejects testbench ERRORs and timeout messages. The final run reports 250 CPU
cycles, 210 retired instructions, one memory read request and two write requests
(one is the exit register). These are smoke diagnostics, not performance results.

Run the simulator and collect the compact evidence from the code-repository root:

```sh
python3 experiments/bounded_dynamic/len5/qualify_simulation.py --tb-compat
python3 experiments/bounded_dynamic/len5/collect_evidence.py
```

The collector checks source-hash equality between synthesis and simulation,
preserved capacities, actual memory traffic, clean smoke completion, and the
dynamic issue witness. It keeps failed attempts. In particular, the historical
`pre_fpu_simulation_pipe2` manifest's old `smoke_passed=true` flag is insufficient:
that run still has trace-monitor errors and is explicitly excluded by the final
summary. The accepted run is `pre_fpu_simulation_ooo`.

## Preserved failed attempt at the current revision

The `current_integer` profile at `5206e92` disables only existing F, D and dummy
coprocessor switches and renames a duplicate disabled-coprocessor generate label.
These are baseline choices, not optimization savings. It elaborates in roughly
six seconds, but the subsequent raw check finds nine multiple-driver problems.
The duplicated load `mem_we_o=0` assignment is
identical on both drivers. More seriously, `csrs.sv:204` continuously drives
FCSR to zero while `csrs.sv:321-385` resets/writes the same eight bits in an
`always_ff` block. Generic CSR accesses still select these FCSR fields even
with F/D disabled. Choosing one meaning would be a semantic repair; none is
applied. Raw evidence remains in `build/integer_frontend/`.

For later simulation, upstream provides FuseSoC/Verilator targets and an RV64
GCC application build, with Spike trace comparison. This directory has not run
that regression. Upstream `make check` excludes `timer`, `alu_mult`, and `alu_div`;
that fact must not be mistaken for evidence those tests pass.

## Genuine dynamic scheduling and interface scope

`rtl/expipe/exec-units/arith_rs.sv:117-148,153-230,350-408` stores pending operands
per entry and independently selects execute-ready entries (`ready_ex`,
`ex_accepted`, CDB wakeup), so this is
not an in-order core with merely out-of-order completion. Its ROB additionally
supports restricted out-of-order commit
(`rtl/expipe/commit-unit/rob.sv:89-167`), so a checker must not
assume all retirement events are in program order.

The [execution witness](results/ooo_witness.json) is stronger than retirement
order alone. In consecutive dispatches within the same reset/flush epoch:

| Instruction | PC | Dispatch | ALU execution/result | Memory response |
| --- | ---: | ---: | ---: | ---: |
| `ld a0,8(t4)` | `0x30` | 238 | — | 247 |
| `addi a2,a0,1` (waiting for the load) | `0x34` | 239 | 249 | — |
| `addi a1,zero,31` (independent) | `0x38` | 240 | 241 | — |

The younger independent instruction actually enters the ALU before the older
waiting ALU instruction. The load is accepted at cycle 244 and returns value 31
at 247; the dependent ADDI then produces 32. These events come from original RTL
handshakes, observed by [qualification_monitor.svh](qualification_monitor.svh).
They establish one concrete dynamic-scheduling trace, not a universal proof.

`rtl/datapath.sv:11-50` exposes instruction and separately tagged load/store
request, grant, response-valid and response-ready ports. The bare datapath has
an optional store-forwarding L0 structure; the separate `rtl-vm` hierarchy is
not selected. Instruction fetch responses have no tags and must remain ordered.

Keep the frontend FIFO parameter fixed in timing comparisons: upstream
`tb/tb_bare.sv:41-49` derives `FetchMemIfFifoDepth` from `MemPipeNum`, and passes
it into the core at line266. Sweeping that testbench variable unchanged would
co-vary hardware capacity with memory latency.
The two-entry FIFO has no empty bypass (`rtl/common/fifo_nohs.sv:119`), so a
same-cycle instruction response consumes old prediction data. A preserved
zero-stage-memory attempt at fixed FIFO 2 timed out; the qualified environment
has delayed instruction responses and a bounded outstanding count compatible
with that fixed FIFO. Any same-cycle load/store timing experiment must keep the
instruction channel's compatible response protocol separate.

See [CANDIDATE_REVIEW.md](CANDIDATE_REVIEW.md) for the actual response-state
opportunity and the rejected truncated-tag candidate. Neither is an executed
Pscorr experiment or an accepted pruning result.
