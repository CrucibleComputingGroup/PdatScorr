# Application validation on RSD

CoreMark and Dhrystone extend the queue-capacity experiment beyond the assembly
diagnostic kernels. These runs use RV32IM plus Zicsr and mutable RAM/stack. They
do not satisfy the no-M ISA assumption or the nonalias-region contract, and no
dependence-cut application result is claimed.

RSD's benchmark folders only contain Makefiles that copy binaries from an
unavailable external `RSD_ENV` tree. `build_applications.py` therefore builds
small platform ports from the workspace's existing vendor sources and retains
their original bytes, hashes, licenses, compiler commands and ELF/hex images.
CoreMark's vendor lock identifies upstream revision
`0c91314d1a4fdfc157d623ad5cb6ac5aef746db1`. Dhrystone uses the existing
`riscv-tests/benchmarks/dhrystone` sources; per-file hashes identify those bytes.

The common port supplies the RSD ROM-to-RAM loader, bytewise libc operations and
UART access. Timer reads use RSD's actual `mcycle` CSR. CoreMark runs all three
algorithms with standard 2 KB validation input `(0x3415,0x3415,0x66)` and ten
iterations. Dhrystone retains its upstream 500-iteration default, separate
compilation and no-inline pragma. Its previously silent debug printer is enabled
so original expected final variables can be checked externally. Both compile
at `-O2` without LTO or builtins. The initial Dhrystone compile failure (printer
declaration return type) is retained in `results/application_build_attempt1/`.

These are validation and cycle-comparison runs, not certified benchmark scores.
The existing Ibex CoreMark vendor patch disables the minimum ten-second check;
the algorithm and all CRC checks remain unchanged. Printed seconds and rates
use a nominal 1 MHz conversion solely to preserve upstream formatting. Use
the actual benchmark-loop cycle deltas below, not the printed rates.

| Application | Iterations | LQ/SQ16 cycles | LQ/SQ8 cycles | LQ/SQ4 cycles |
| --- | ---: | ---: | ---: | ---: |
| CoreMark, 2 KB validation | 10 | 3,336,042 | 3,388,858 | 5,018,931 |
| Dhrystone | 500 | 255,757 | 285,571 | 575,158 |

All six runs reach PC `0x1004`, finish before the cycle/wall-time limits and pass
the original validation expectations. CoreMark's seed/list/matrix/state CRCs
are `18f2/e3c1/0747/8d84`; its final CRC is `c64e` in all three runs.
Dhrystone checks all printed final scalar/string/record values and the expected
pointer equality. Serial outputs match byte-for-byte after removing timing
lines. Baseline16 uses the original uninstrumented binary; queue8/4 use the
previously validated nonintrusive tracing binaries. Source cache, MSHR, ROB,
issue and front-end configuration remain unchanged across capacities.

`results/application_summary.json` and `.csv` contain measured ratios, whole
program cycles, input/binary hashes and the comparison audit. Raw output,
input images and run commands are under `results/apps_lq{16,8,4}_sq{16,8,4}/`.

```bash
# Fresh output paths are required to preserve prior evidence.
bash experiments/rsd_ooo/bootstrap_rsd.sh
bash experiments/rsd_ooo/bootstrap_verilator.sh
python3 experiments/rsd_ooo/build_applications.py --output /tmp/rsd-applications
for size in 16 8 4; do
  python3 experiments/rsd_ooo/build_simulations.py --size "$size" \
    --name "application_repro_lq${size}_sq${size}"
  python3 experiments/rsd_ooo/run_applications.py \
    --applications /tmp/rsd-applications \
    --binary "experiments/rsd_ooo/results/application_repro_lq${size}_sq${size}/VMain_Zynq_Wrapper" \
    --output "experiments/rsd_ooo/results/new_applications/apps_lq${size}_sq${size}"
done
python3 experiments/rsd_ooo/summarize_applications.py \
  --results-root experiments/rsd_ooo/results/new_applications
```

The default summarizer audits the retained six-run dataset; `--results-root`
selects a fresh six-run dataset. The recipe builds monitored versions at all
three capacities; the retained16 result used the uninstrumented upstream
harness. Monitoring changes only observation, not core RTL. `bootstrap_rsd.sh` verifies
the pinned clean checkout and records host/cross-tool and libgcc identities;
it verifies an identical existing manifest or records a new timestamped one
when tool identities differ. `bootstrap_verilator.sh`
builds the pinned local tool required by `build_simulations.py`.
