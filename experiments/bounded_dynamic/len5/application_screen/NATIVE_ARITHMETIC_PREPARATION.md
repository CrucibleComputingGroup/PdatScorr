# Retaining native arithmetic after closed inactive-FU facts

The matched second preparation uses `--datapath-abstraction none`. It retains
the original ALU result, including the loop counter and address calculations,
after importing the same certified decoder, seven word-domain theorems, ROM
closure, and 1,761 program-derived reset facts. It adds no premise or source
hardware change. Preparation itself runs no target solver.

| Proof model | AIG ANDs | AIG latches | AIG inputs |
|---|---:|---:|---:|
| Inactive-FU facts plus ALU/multiplier abstraction | 493,830 | 20,968 | 31,255 |
| Same facts, native arithmetic retained | 522,336 | 22,024 | 32,247 |

Native arithmetic costs 28,506 additional AND nodes and 1,056 latches in this
proof representation. The model still has fewer AND nodes than the earlier
530,756-AND ALU/multiplier abstraction without the inactive-FU facts. These
are proof-model sizes, not physical area or accepted hardware savings.

Both preparations have exactly three assertions and eight assumptions:
initial reset and the seven independently proved word-domain conclusions.
Both verify the same 269 transitive dependencies. The source JSON, native
`core.json`/`core.v`, external harness, seven-lemma graph, inactive-FU graph,
and preparation driver are byte-identical. Only the first preparation then
applies the payload abstraction. Native hardware JSON SHA256 is
`2426b17743dfc23d806d5c544f9c6ebbc722909ed01442f0cb41403a11ad4b48`.

The second final query is exactly `inactive_query_core.json`, SHA256
`7406d6177bcdc33f3b1c0d7d13510f262fe301bb026b81b444c8137e86e623cc`.
Its AIG SHA256 is
`664d43bfd5c703da92f194eb121862dc395992e076e3ec2c1dd3430878f8dc6d`.
The source-bound preparation is
`build/harvard_rom_inactive_fu_native_prepare_v1`; compact evidence is
`evidence/inactive_fu_native_preparation_v1`. The executable comparison and
its results are in `compare_inactive_preparations.py` and
`review/inactive_arithmetic_comparison_v1`. The independent whole-graph
review is recorded separately in `review/inactive_fu_native_v1`.

Use the preparation recipe in `INACTIVE_FU_IMPORT.md` with a fresh output
directory and `--datapath-abstraction none`. The evidence package records the
exact source files, command lines, proof dependencies, and hashes. No new
MUL-only abstraction was introduced. Solver diagnostics, if authorized, are
separate artifacts and do not turn this preparation into an accepted
optimization.
