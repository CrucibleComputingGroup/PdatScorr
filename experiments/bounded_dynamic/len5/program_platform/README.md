# ELF-derived Harvard program platform

This platform separates the streaming kernel's executable instructions from its
input data. The same 14 instructions occupy 56 bytes at address zero in an
allocated executable `.text` section and an RX `PT_LOAD` segment. The 64 uint64
inputs and 128 zero padding bytes occupy `.rodata` at `0x1000` in a separate
non-executable R segment. The instruction bytes exactly match the earlier
streaming kernel; neither instructions nor core RTL/capacities are changed.

`elf_images.py` selects **all allocated executable sections** using
`SHF_EXECINSTR`, checks agreement with the covering segment's `PF_X`, and emits
`instruction.hex`. All other allocated contents form `data.hex`. No opcode list
selects the ROM bytes. Independent GNU `objcopy` section extraction agrees with
both images. The ELF, linker script, source, section/segment report, images, and
hash manifest are retained in `evidence/streaming_v1`.

The declared external platform uses separate memory objects: immutable
instruction ROM and mutable sparse byte-addressed data RAM. Data RAM starts
with `0x1000..0x127f` mapped; upstream data writes create/update bytes, including
the outputs at `0x2000..0x21ff` and the exit mailbox at `0x20000100`. Input data
cannot become executable, and data writes cannot modify the instruction ROM.
This is a deliberate Harvard-platform definition, not a claim that every
behavior matches the previous unified-memory testbench.

`platform_patch.py` replaces only the original memory model's combinational
instruction lookup. The replacement checks alignment first, then requires all
four instruction bytes to exist. Misaligned and unmapped requests produce
their instruction exception codes and a defined **zero instruction payload**;
successful reads return exactly the ELF word. When no request is present,
payload is zero and code is `E_UNKNOWN`. No data-memory operation is replaced.
Every byte of the native instruction/data pipelines, readiness, flush handling,
and data-memory access code outside that lookup block is preserved.

The unchanged native fetch pipeline has two stages, advances with response
readiness, and clears on flush edges. The external acceptance gate enforces a
minimum two-cycle request gap; flush does not reset its cooldown. The native
data path retains three-cycle tagged responses and does not flush data replies.
`qualify_simulation.py --harvard-rom --build-only` builds this simulator. The
build-only flag explicitly skips the old unified-image smoke; the separate-image
runner supplies its own application checks.

The finite qualification passed all 64 expected output stores plus exit zero,
using 931 reported CPU cycles. It contains 64 actual ALU issue inversions:
in the first witness, the older load-dependent ADDI dispatches at cycle 24 and
executes at 30, while the younger independent pointer ADDI dispatches at 28 and
executes at 29. All 484 completed fetches take two cycles, and all 65 completed
loads take three cycles. No completed fetch/load faults occur. The instruction
response payload stays within the 14 ELF words plus zero even on invalid cycles.
These finite results do not prove a universal occupancy bound or an optimization.
In particular, the absence of data faults is established only for this recorded
run. The sparse data RAM can fault on other unmapped or misaligned accesses;
there is no universal data-address/range claim. A formal harness that supplies
fault-free arbitrary data therefore defines a separate nonfaulting service
domain unless data-fault exclusion is independently proved.

`check_platform.py` compiles the actual patched memory module independently. Its
70 checks cover every text-byte offset, alignment and ROM boundaries, the data
region, maximum addresses, zero fault payloads/codes, independent SystemVerilog
`$readmemh` reference values, and separation from data writes. It also checks
all 74 compiled core source files directly against the official pre-FPU git
objects at `14291dcc5bef181085d001c5a29e7f4fc4cbc8e9`, and checks that the memory
module differs solely in the declared lookup replacement. Results are in
`evidence/platform_checks_v1`.

Reproduce from the code repository (the qualified source/dependency setup from
the parent LEN5 directory must already exist):

```sh
python3 experiments/bounded_dynamic/len5/qualify_simulation.py \
  --build /tmp/len5-harvard-build --instruction-min-spacing 2 \
  --memory-pipe-num 2 --tb-compat --harvard-rom --build-only
python3 experiments/bounded_dynamic/len5/program_platform/run_platform.py \
  --simulator-build /tmp/len5-harvard-build \
  --output /tmp/len5-harvard-program --evidence /tmp/len5-harvard-evidence
python3 experiments/bounded_dynamic/len5/program_platform/check_platform.py \
  --build /tmp/len5-harvard-build --program /tmp/len5-harvard-program \
  --output /tmp/len5-harvard-check --evidence /tmp/len5-harvard-check-evidence
```

Run/evidence/check directories must be fresh. The runner compares its 56 code
bytes against the earlier frozen `streaming_fetchgap2_v2/program.hex`; another
copy can be supplied with `--reference-image`. Large binaries, full source
snapshots, and waveform dumps remain in the external ignored build area. Each
compact evidence directory has its own `SHA256SUMS`.
