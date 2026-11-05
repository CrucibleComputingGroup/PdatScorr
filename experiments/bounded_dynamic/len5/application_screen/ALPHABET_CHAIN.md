# Instruction-alphabet dependency-chain screen

The suggested simple dependency chain did **not** refute the proposed low-slot
exclusion for the gap-2 platform. The unchanged qualified simulator ran
`lui s0,0x1`, 64 copies of `addi s0,s0,8`, and the original allowed exit sequence.
All instruction words, including mapped speculative padding after the halt,
belong to the streaming kernel's original 14-word alphabet. This is a different
program from the exact streaming kernel.

The host checked all 64 retired ADDI instructions, PCs, destination register,
and values `0x1000 + 8*i`, plus the sole exit store. The program exits with code
zero in 143 reported CPU cycles. It reaches maximum ALU occupancy one and uses
only indices 6 and 7. The trace has 97 accepted fetches, all separated by two
cycles; all 94 complete replies take two cycles. Two requests are canceled by
flush and one remains pending at the end. There are no load requests or raised
instruction/load exception flags. The trace shows each dependent ADDI starts
and returns its ALU result one cycle after dispatch, before the next dispatch.

Thus this particular dependency chain does not accumulate enough live entries
to refute the candidate. It establishes no universal occupancy bound and gives
no correctness guarantee for rewriting the exact kernel or broader alphabet.

`evidence/alphabet_chain_gap2_v1` contains 18 files (190,059 bytes): source,
disassembly/image, simulator manifest, logs, retired-value checks, edge/response
CSV, occupancy CSV, selected RS waveform, summary, and SHA manifest. All 17
payload hashes pass. The full FST/VCD remains under
`/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build/alphabet_chain_gap2_v1`.
The summary records their hashes and all source/tool/build identities.

Reproduce into fresh directories without rebuilding the core:

```sh
python3 experiments/bounded_dynamic/len5/application_screen/run_alphabet_falsifier.py \
  --output /tmp/alphabet-chain-run --evidence /tmp/alphabet-chain-evidence
```
