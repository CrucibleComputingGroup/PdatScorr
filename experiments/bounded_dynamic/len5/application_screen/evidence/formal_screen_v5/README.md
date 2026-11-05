# Formal admission-screen evidence (v5)

**No optimization is accepted.** The original-core v3 query reached PDR frame7
and timed out; the v5 proof abstraction reached frame8 and timed out. v5 replaces
only two 64-bit combinational ALU/MUL result drivers with symbolic values.
This admits all original traces plus extra behaviors; it is not native hardware
and its cone/state counts are not area savings.

The bounded diagnostic found an abstract ALU admission violation at frame 19. Both readiness assertions are constant true in the prepared model, leaving only the ALU admission prohibition. ABC validated the retained witness on the same abstract AIG. Native-core concretization remains unresolved; this is not a native occupancy counterexample. See PROVENANCE.json and v5/bounded_screen/.

Version history: v1/v2 used a queue-age instruction service that did not match
native readiness/flush behavior; v1 also failed residual-memory validation and
v2 stopped in ABC export. v3 corrected the fetch handshake but used0 instead of
native31 for successful response exception codes. v4 corrected codes/source
binding and introduced proof-only ALU/MUL abstraction, but Verilog rereading
failed on `$anyseq`. v5 reads the core JSON directly, preserving those symbols.
No failed, timed-out or bounded-only run is treated as proof.

The v3 trace audit and source review are under review/. v5's source manifest,
original pin, exact cuts, scripts, harness, logs and hashes are retained. Large
JSON/Verilog models remain external with hashes in PROVENANCE.json. When a
witness exists, v5/screen.aig.gz retains its exact AIG and symbol order; decompress
before using it. Large text logs are retained losslessly as .log.gz. The large
named witness listing remains external with its hash and regeneration command;
the machine AIW and validation records are included. The instruction alphabet is independently checked against the
included padded-kernel disassembly. Source files are verified against upstream
git objects at the exact pinned revision.

The sound data-abstraction relation is under the same **instruction-alphabet
environment**. Recorded kernel fetches all belong to that alphabet, but no
unbounded theorem excludes other padding/data words from the actual ROM.
The frozen runner's general ROM-overapproximation wording exceeds that evidence;
this package establishes finite trace inclusion and alphabet-domain screening.

Reproduction from the code-repository root (fresh output paths):

```sh
python3 experiments/bounded_dynamic/len5/prepare_frontend.py --profile pre_fpu
python3 experiments/bounded_dynamic/len5/application_screen/formal_screen.py \
  --disassembly experiments/bounded_dynamic/len5/application_screen/evidence/formal_screen_v5/inputs/program.disasm \
  --output /tmp/len5-admission-review --gap 2 --threshold 4 \
  --datapath-abstraction alu_mul --timeout 120
```

Verify the current runner/helper hashes against v5/ before reproduction. The
PDR and bounded ABC command lines are recorded verbatim in their run summaries.
Tool versions are bound by executable hashes. Collect this review into a fresh
directory with `application_screen/collect_formal_screen.py --output PATH`.
The collector does not run experiments. SHA256SUMS covers every package file
except itself; PROVENANCE.json distinguishes original-run and review-time hashes.
