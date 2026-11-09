# Pscorr netlists for FlexIC area: Rocket, CVA6, Ibex

This folder holds the Pscorr-optimized netlists behind the paper's area numbers, plus a
script that maps them to any Liberty library and tabulates the area. To get FlexIC
numbers, point the script at the FlexIC Liberty file. Nothing else needs to be rerun:
the Pscorr optimization is technology-independent, and only the final cell mapping
depends on the library.

## Quick start

```bash
cd /mnt/shared/shared/pscorr_flexic
python3 run_all.py --liberty /path/to/flexic.lib --jobs 4 --out ~/pscorr_flexic_results
```

This writes:

- `results.csv`: one row per design, with its area, its reference's area, and the
  normalized area;
- `summary.txt`: the paper's statistics per study:
  - Rocket and CVA6: geomean, max and min reduction against RV32IM;
  - Ibex: the reduction from timing constraints.

`--only ibex/` (or `rocket/`, `cva6/`, or any part of a design id) runs a subset; a
workload's reference is always included. Rerunning with the same `--out` skips
designs that already have an area.

Time per design on this server with SKY130:

- Ibex: 13–20 s;
- Rocket: 15–25 s;
- CVA6: 3–4 min.

The whole set of 70 designs took 27 min with 4 jobs.

## Sanity check: reproduce the paper's SKY130 numbers

`check_sky130/` holds a full run of this folder with the SKY130 HD library that the
paper used (Yosys 0.33, `/usr/bin/yosys` on this server). All 70 designs reproduce
their recorded SKY130 area in `manifest.csv` exactly. `check_sky130/summary.txt`
reproduces the paper's statistics:

- Rocket: geomean 10.1%, up to 25.9%;
- CVA6: geomean 3.45%, up to 9.14%;
- Ibex Table 4: 0.19%, 0.13% and 0.16%.

To repeat the check for one core:

```bash
python3 run_all.py --only ibex/ --out /tmp/check \
  --liberty /mnt/shared/pdk/skywater-pdk/libraries/sky130_fd_sc_hd/latest/timing/sky130_fd_sc_hd__tt_025C_1v80.lib
```

## What is included

| Core | Paper item | Designs | Normalized to |
|---|---|---|---|
| Rocket (TinyRocket, RV32IMA, 5-stage) | Fig. 4 | 21 workloads | each workload's own RV32IM run (21 runs; same SKY130 area) |
| CVA6 (cv32a60x, in-order, HPDcache) | Fig. 4 | 21 workloads | one RV32IM run |
| Ibex (`ibex_core_with_rf`) | Table 4 | RV32IM, RV32IM_no_mul, RV32I | the same ISA without timing constraints |

Each design is in `designs/<core>/<name>/`:

- `optimized.aig`: the Pscorr output, exactly the netlist the paper mapped;
- `optimized_generic.v`: the same netlist as technology-independent Verilog, for use
  with another synthesis tool;
- `constraints.sv`: the CRISP-generated assumptions used to optimize it, for reference.
  The Ibex timing designs also have `constraints_isa.sv`.

`manifest.csv` lists each design's top module, clock, recorded SKY130 area, AIG
SHA-256, and the original run folder.

Ibex Fig. 3 (register count, ISA subsets, data width) is not included yet; see the
note at the end.

## What the area counts

The area is the standard cells (logic and flip-flops) inside each core's boundary, as
in the paper.

- **Rocket:** the wrapper exposes the instruction and data memory interfaces, so caches
  are not included.
- **CVA6:** the I$ and D$ SRAM arrays are black boxes whose pins became ports, so they
  are not included. The cache controllers, MSHRs and write buffer are included.
- **Ibex:** the register file is built from flip-flops and is included.

If FlexIC totals should include memory arrays, add their area separately; it is the
same in every design.

## Mapping recipe

`map_area.sh LIBERTY AIG TOP CLOCK OUT_PREFIX` runs the exact Yosys commands behind the
paper's numbers:

1. `read_aiger`, then generic optimization;
2. `dfflibmap -liberty` for flip-flops;
3. ABC's `strash; dretime; map` with the Liberty file for logic. This is the script
   that `abc -fast` runs in Yosys 0.33. Newer Yosys no longer accepts `-fast`, so the
   script is given explicitly; with Yosys 0.33 both give identical netlists;
4. `stat -liberty` for the area.

Area is in the Liberty file's area unit (µm² for SKY130).

The library needs a D flip-flop for `dfflibmap`. If any internal Yosys cell is left
unmapped (for example `$_DFF_P_`), the `note` column in `results.csv` names it, and the
area is then incomplete.

If you use another synthesis tool, synthesize `optimized_generic.v`. Use the top and
clock from `manifest.csv`, and apply the same flow to every design.

Yosys 0.33 reproduces the SKY130 numbers exactly. Newer versions also run, but shift
the areas slightly. With a Yosys 0.70 build, the SKY130 geomean reduction is 10.1%
for Rocket (unchanged) and 2.9% for CVA6 (3.45% with 0.33); see
`check_sky130_yosys070/`. Use one version for all designs.

## Provenance

The bundle was built by `build_bundle.py` from the archived runs listed in
`manifest.csv`. Each AIG was checked against the SHA-256 recorded for its run. The
scripts are in the Pscorr code repository, branch `feat/bounded-dynamic-odc`, under
`experiments/bounded_dynamic/stock_pscorr/flexic_bundle/`.

## Not yet included: Ibex Fig. 3

The netlists for Fig. 3 were produced in a different environment and are not on this
server: register count (4, 8, 16, 32), ISA subsets (RV32IM, RV32I, No Shifts, No
Branches, Arith Only) and data width (8, 16, 24 bit).

The 32-bit point has the same SKY130 area as Table 4's RV32I without timing
(`designs/ibex/table4_rv32i`).

When the other netlists are available, they will be added as `designs/ibex/fig3_*`
with matching rows in `manifest.csv`.
