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
  - Ibex Table 4: the reduction from timing constraints;
  - Ibex Fig. 3: each configuration's area relative to its group's reference.

`--only ibex/` (or `rocket/`, `cva6/`, or any part of a design id) runs a subset; a
workload's reference is always included. Rerunning with the same `--out` skips
designs that already have an area.

To map only the 13 Ibex Fig. 3 designs:

```bash
python3 run_all.py --liberty /path/to/flexic.lib --only ibex/fig3 --jobs 4 --out ~/pscorr_flexic_fig3
```

Time per design on this server with SKY130:

- Ibex: 13–20 s;
- Rocket: 15–25 s;
- CVA6: 3–4 min.

The first 70 designs took 27 min with 4 jobs. The 13 Ibex Fig. 3 designs take under a
minute.

## Sanity check: reproduce the paper's SKY130 numbers

`check_sky130/` holds a full run of this folder with the SKY130 HD library that the
paper used (Yosys 0.33, `/usr/bin/yosys` on this server). All 83 designs reproduce
their recorded SKY130 area in `manifest.csv` exactly. `check_sky130/summary.txt`
reproduces the paper's statistics:

- Rocket: geomean 10.1%, up to 25.9%;
- CVA6: geomean 3.45%, up to 9.14%;
- Ibex Table 4: 0.19%, 0.13% and 0.16%;
- Ibex Fig. 3: 47.3% for 4 registers, 34.7% for arithmetic only, 47.6% for 8-bit data.

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
| Ibex | Fig. 3(a) | 32, 16, 8, 4 registers | 32 registers |
| Ibex | Fig. 3(b) | RV32IM, RV32I, No Shifts, No Branches, Arith Only | RV32IM |
| Ibex | Fig. 3(c) | 32-, 24-, 16-, 8-bit data | 32-bit |

Each design is in `designs/<core>/<name>/`:

- `optimized.aig`: the Pscorr output, exactly the netlist the paper mapped;
- `optimized_generic.v`: the same netlist as technology-independent Verilog, for use
  with another synthesis tool;
- `constraints.sv`: the CRISP-generated assumptions used to optimize it, for reference.
  The Ibex timing designs also have `constraints_isa.sv`;
- `register_file.sv`: only for the Fig. 3 designs with fewer or narrower registers, the
  register file they were synthesized with.

`manifest.csv` lists each design's top module, clock, recorded SKY130 area, AIG
SHA-256, and the original run folder.

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
`check_sky130_yosys070/`, which covers the first 70 designs. Use one version for all
designs.

## Provenance

The bundle was built by `build_bundle.py` from the archived runs listed in
`manifest.csv`. Each AIG was checked against the SHA-256 recorded for its run. The Ibex
Fig. 3 designs come from regenerated runs and were checked against the paper's record
instead; see the next section. The scripts are in the Pscorr code repository, branch
`feat/bounded-dynamic-odc`, under
`experiments/bounded_dynamic/stock_pscorr/flexic_bundle/`.

## Ibex Fig. 3 designs are regenerated

The netlists of Fig. 3 were not archived, so the 13 designs `designs/ibex/fig3_*` were
regenerated with the paper's experiment checkout. `ibex_fig3/` in the code repository
holds the recipe and the comparison with the values recorded for the paper:

- 11 designs reproduce the recorded AND gates, SKY130 area and FMax exactly;
- the 8- and 4-register designs differ in area by 0.005% and 0.02%. `manifest.csv`
  records the area of the bundled netlist: 53531.3408 µm² (paper: 53528.8) and
  47324.1376 µm² (paper: 47314.1).

"32 regs" and "RV32I" are the same configuration, run once in each group. The 32-bit
point is the configuration of Table 4's RV32I without timing.
