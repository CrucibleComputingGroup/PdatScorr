# Timing constraints to automatic ODC optimization

The user approved this study on 2026-11-04. Its purpose is to enhance Pscorr:
timing and microarchitectural restrictions constrain possible executions;
Pscorr must automatically relate those restrictions to unobservable logic or
state and produce a smaller implementation. A manual ROB/RS/LSQ capacity sweep
does not establish this contribution.

## First demonstrated result

**Research decision:** the user judged the 0.893% component gain too small for
the paper. Retain this case as a mechanism and regression test. The main study
must target substantial automatically removed RS/LSQ storage and assess its
whole-core impact; do not promote this small result into a manuscript section.

The automatic flow finds and proves two response-tag equality reductions in the
original RSD component, with all capacities and state-update drivers unchanged.
Under accepted-read spacing of at least three cycles, responses within five
cycles, and ordered responses, each two-bit comparison can use its low bit.
The two-copy PDR proof checks all 545 defined functional output bits and the
combined transformed design. It uses no imported allocator lemmas.

Matched SKY130 mapping of the certified native hardware pair gives **335 -> 333
flip-flops** and **17,513.0464 -> 17,356.6464 square micrometres (0.893%)**. This
is a small component mechanism result, not whole-core area or application
validation. The source cone and timing constraints are supplied by the user of
the tool; candidate generation, certification, and rewriting are automated.

The inherited constrained `scorr` flow also optimizes its formal model. Applying
it to original versus automatically transformed hardware gives 5,445 versus
5,417 AND nodes and 342 versus 340 encoded latches. Those counts include formal
encoding and must not be compared directly with native mapped area. The evidence
supports an additional automatic native-RTL rewrite; it does not establish a
physical-area advantage over a recovered native implementation from `scorr`.

See [the audited hardware/proof/map record](rsd_mshr/evidence/final/summary.json),
[the experiment and constraints](rsd_mshr/README.md), and
[matched correspondence controls](rsd_mshr/control/README.md).

## Fixed comparison and acceptance criteria

- Preserve original RTL and all capacities across method comparisons. A fixed
  integer configuration is allowed when selecting a core, but disabling units
  is not an optimization result.
- Use the same external constraints, reset/initial-state semantics, observed
  outputs, synthesis library, and resource limits. Internal facts must be
  derived and proved, never added as unexplained assumptions.
- Generate candidates from elaborated hardware, prove the actual transformed
  design, and let ordinary synthesis remove dead logic. Individually proved
  changes require a combined proof before use.
- Reject timeouts, bounded-only success, vacuity, missing properties, stale
  artifacts, and synthetic reports. Keep observable-mutation and relaxed-timing
  negative controls, plus covers showing genuine concurrent activity.
- Report component versus full-core evidence and formal-encoding counts versus
  physical hardware area separately. Do not put new claims in the manuscript
  before the mechanism and its intended scope have been validated.

## Implementation

`odc/temporal.py` and `scripts/analyze_temporal_odc.py` enumerate unsigned equality
cells in a selected source cone. Each proposed low-bit comparison is a netlist
rewrite, not an extra driver or a manually cut source file. A fixed two-copy
miter checks every supplied functional observation under an immutable reference
environment. The proof backend uses reset-base checking plus temporal induction,
or PDR over the complete sequential miter. The latter discovers its own
invariants; it does not import the hand-written explanatory allocator lemmas.

Arbitrary uninitialized payload state is correlated between the two copies only
at time zero. An additional state-correspondence **assertion** helps induction;
it is not a continuing equality assumption. Explicit initialization differences
are rejected. The physical mapper reads the certified hardware pair directly,
without formal monitors or the additional state used by AIGER initialization.

The checker audit in `review/odc_pipeline_review.txt` also motivated fail-closed
repairs to legacy ODC checking. These repairs do not certify historical results
or repair every legacy injection and rewriting path.

## Targets

`rsd_mshr/` is the first small mechanism experiment using original RSD MSHRs,
request arbitration/routing, and the original read-ID free list. Capacities
remain fixed. Bounded, ordered response service can make a high response-tag
comparison bit unobservable while both MSHRs operate and IDs wrap. The local
invariant proof explains the mechanism; the generic miter must independently
certify the automatically generated candidate before any savings are reported.

LEN5 is qualified as a smaller complete OoO core. Its older official
integer revision avoids an unrelated CSR multiple-driver problem in the current
floating-point-capable revision. A short response deadline alone does not
justify deleting queue slots or narrowing every comparator: the LEN5 load
buffer can accept a response in a slot that has not yet issued its request.
The unchanged-RTL smoke includes an actual younger independent ALU instruction
executing before an older load completes and before an older dependent ALU
instruction. [Qualification evidence](len5/README.md) is separate from the RSD
optimization result.

Builds, cloned cores, solver models, and large traces are excluded from Git.
Keep reproducible preparation scripts, pinned revisions, compact evidence, and
hashes here. The old `experiments/rsd_ooo` directory is archival exploratory work,
not evidence for the redesigned contribution.
