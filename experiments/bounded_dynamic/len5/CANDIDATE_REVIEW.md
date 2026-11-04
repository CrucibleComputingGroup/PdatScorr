# Timing candidates: source review, no accepted transformation

All references below use the pinned upstream commit
`5206e92bc7235cd1cbcc10522aaee3f69f9b5e7b` and paths relative to its root.
The later-qualified official pre-FPU revision `14291dcc5bef181085d001c5a29e7f4fc4cbc8e9`
has identical load/store buffer timing and allocator behavior. The only LB/SB
source changes between these revisions add zero-valued FP flag fields to CDB
outputs; references after those additions shift by one line in the older source.

## Same-cycle service can make memory-wait states unreachable

In `rtl/expipe/load-store-unit/load_buffer.sv:234-270`, a matching response in
`LOAD_S_MEM_REQ` takes priority over the transition to `LOAD_S_MEM_WAIT`.
`store_buffer.sv:274-286` has the corresponding store rule. Both response-ready
outputs are permanently one (`load_buffer.sv:410`, `store_buffer.sv:429`).

A precise same-cycle contract is, for each load/store channel while operating,
`response_valid == request_valid && request_grant`, with the response tag equal
to the accepted request tag when valid. Response data and exception results
remain unconstrained by this timing restriction. Reset/flush cancellation and
memory-data consistency must be stated by the integration harness; no unsolicited
or delayed responses may be silently introduced. Request grant can still stall,
so this contract does not itself bound queue occupancy or instruction lifetime.

Reset initializes every state to EMPTY. If MEM_WAIT is absent in the present
state, accepted requests are answered in MEM_REQ and cannot enter MEM_WAIT;
other transitions do not enter it. This is a source-level inductive argument
to test on the actual RTL, not a discharged proof or a measured saving.

The automatic experiment must derive/prove the state fact and let Pscorr find
and validate useful transformations. Do not manually change the state machine
or count baseline configuration switches as the result.

Consumer limits: load result storage is still needed until CDB arbitration/pop
(`load_buffer.sv:272-274,338-349,386-392`). Completed stores can become CACHED
(`store_buffer.sv:288-297`) and supply future loads via `l0_cached_*` outputs
(lines412-424). A quick memory response does not make these payloads dead.
Full reset/observation protocols must match the unconstrained control.

## Rejected: narrow every response-tag comparison to low two bits

Proposed premise: each accepted load request receives exactly one response
within at most two cycles, so fewer than four request tags can be outstanding.
That premise does **not** establish that low two bits identify every consumer
of a response comparison.

Source-level counterexample construction (not a simulator trace):

1. Keep request grant low while five independent loads occupy slots0 through4
   of the unchanged eight-entry LB and finish address generation. They can all
   be in MEM_REQ; the memory pointer still names slot0.
2. Grant slot0, then return its response tag0 on the next cycle. The latency
   bound is satisfied. Slot0 is MEM_WAIT, while slot4 is still MEM_REQ and has
   never sent a request.
3. Full comparison accepts the response only for slot0. Low-two-bit comparison
   also matches slot4 in its MEM_REQ branch, stores the wrong data there, and
   transitions it to COMPLETED. Subsequent memory-pointer progress/CDB output
   can differ. This is not an unobservable inactive entry.

The decisive source is `load_buffer.sv:239` (and250 without forwarding): the
MEM_REQ response comparison is not gated by `mem_idx==i` or prior acceptance.
Acceptance is a separate later branch at lines246/257. The state/data effects
are at lines245/256 and338-339; CDB selects completed head entries at386-392.
Store-to-load forwarding does not rescue this construction: choose no stores,
so no forwarding hit occurs. No exception or flush is required either.

Narrowing only the MEM_WAIT comparison might be provable with bounded legal
responses, no stale response after flush, and the at-most-one-pointer-step per
cycle invariant (`load_buffer.sv:169-174`). But the full comparator remains
needed by MEM_REQ and may be shared by synthesis; there is no assured area gain.
Adding a new manual acceptance guard would change the candidate and require
its own equivalence proof. Neither alternative is claimed as implemented.

Circular slot indices also remain unrestricted by low occupancy: any slot can
eventually be used. No candidate here deletes upper-numbered slots or resizes
ROB/RS/LB/SB resources.
