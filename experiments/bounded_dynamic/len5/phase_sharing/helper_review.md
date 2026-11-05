# Independent proof-helper review

The three helpers in `proof.py`, `factor_state.py`, and `last_writer.py` were
reviewed against the full original/candidate relation. `helper_review.json`
records source hashes and the focused test command: **108 tests passed**,
including 14 new tests in `tests/unit/test_native_state_certificates.py`.
These are generic toy regressions and a source review; native LEN5 proof
completion must be established by its separate solver artifacts.

The current wrapper additionally uses the shared symbolic-undefined frontend.
The reviewed `assert_native_correspondence` function is AST-identical to its
archived version; the factoring and last-writer helpers are unchanged. The
implementation owner checked the migrated wrapper with active-X rejection and
inactive-X equivalence cases, together with the helper suites: 34 tests passed.
The JSON retains historical hashes and separately records this migration. This
does not retroactively certify historical frontend handling of undefined
choices; prior positive subproofs need revalidation or an irrelevance argument.

`assert_native_correspondence` matches native FF Q bits before `async2sync`.
Duplicate aliases are deduplicated; every edge involved in one-to-many or
many-to-one matching is excluded. It adds an unconditional equality assertion
without an initial-state pairing assumption. This can make a proof harder,
but it cannot authorize an unproved equality merely from matching names.

`factor_common_state` shares only one-to-one matched Q bits, retains the
reference's actual FF transitions, and removes only corresponding candidate
FF bits. Its base requires the sole assumption to be initial native active-low
reset, with both FFs directly using that reset and identical binary reset
values and clocks. Its step asserts equality of both original effective next
values, including enable polarity and reset dominance, before aliasing Q.
If every obligation passes, a first-divergence argument relates every reduced
trajectory to the original pair: the reset gives equality initially, and the
checked next-state relation preserves it. Remaining state is neither replaced
by fresh inputs nor made arbitrary each cycle.

One issue found during review was acceptance of matching unknown reset values:
two independent `x` reset values do not establish equal state. The owner added
a binary-reset guard; the rejection regression passes. Duplicate combinational
drivers are also now rejected before interpreting the initial-reset premise.

`add_last_writer_assertion` keeps both original banks and the candidate shared
bank. Its proof-only register tracks which original bank was written last,
respecting enable polarity and reset. The relation between that selected
original value and the shared value is asserted, not assumed. The common-state
helper excludes all ambiguous bank-Q aliases, so it cannot erase the values
whose lifetimes are being checked. The monitor belongs only to the proof miter.

The tests exercise actual SMT base and induction checks, rather than mocked
success statuses. They prove enabled-state identities with both polarities and
a partial-bank factor, and reject an incorrect D function, inverted candidate
enable, missing reset premise, and unknown reset values. Combined factoring
and last-writer tests retain an actual three-bit reference history counter,
prove a safe four-bit bank share, and obtain bounded counterexamples for wrong
shared-bank priority and exclusive writes with overlapping live values. The
wrong-D test is particularly relevant: after Q aliasing the functional output
comparison is tautological, so the original next-state obligation must still
detect the error.

The reduction remains restricted to the checked initial-reset and single-clock
model. It is not a general justification for arbitrary initial-state sharing,
changing clocks/resets, or omitting output observations. A timeout or unknown
result on the transformed miter remains unproved; generic toy successes do not
convert a native candidate timeout into success. Hardware savings must be
measured from the candidate hardware without these proof-only helpers.
