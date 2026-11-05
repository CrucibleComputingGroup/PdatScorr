# Independent native EU-register lemma review

No soundness blocker was found in the frozen v1 evidence. This review performs
source/projection/hash checks and a finite mux-equation check only; it launches no
solver query and edits no owner source.

The proof chain is closed under initial reset and the certified program-word
domain: decoder equivalence transfers to the exact specialized decoder, whose
assigned-EU high bit **202160** is unconditionally zero. The one-bit native
issue-register projection proves visible bit **91687** zero by base plus induction.
The exact native one-hot demux and valid AND then prove MUL issue bit **67868** and
DIV issue bit **71113** zero. Those bits alias the actual respective unit inputs.
No perpetual unit-idle premise is added. The two local assumptions are conclusions
of preceding proofs, not new environmental restrictions.

The native `$aldff` slice preserves its real rising clock, active-low asynchronous
reset, reset value zero, D/Q identity, and all three mux slices. Both the inner
X-producing mux and outer zero-masking mux use the **same flush bit 91658**;
enable bit **91511** is separately arbitrary. Their exact combined D equation is
`flush ? 0 : (enable ? decoded_high : visible_high)`, independent of the masked X.
Undefined values are symbolized before mapping or preparation, preserving this
correlation. The proof introduces no assumptions on enable or flush.

The observation is the original **visible** register output. After `async2sync`,
the asserted output is `rst_ni ? internal_Q : 0`; the internal Q has no initialization
attribute and is not the claimed theorem target. Importing the invariant onto an
unrelated lowered internal Q would be unsound and is not justified by this result.

The register negative control removes only the derived decoder-high premise and
reaches visible high=1 at step 2. The dispatch negative control removes only the
registered-high premise; selector `100` permits MUL valid=1. All eight recorded
top-level dependencies and all 37 packaged artifact copies match their authoritative
sources. `summary.json` additionally binds the exact candidate decoder diagnostic,
native source, reconstructed slices, proof models, logs, and scripts.

This establishes program-only native control facts. It does not establish the
reset values of all MUL/DIV reservation-station state, invalidate raw inactive
outputs, prove an admission bound, or authorize a hardware rewrite. Further native
reset and consumer/output closure is required before removing storage or claiming
area savings. Applying the conditional theorem to the declared Harvard platform
uses the separate external-ROM domain proof.
