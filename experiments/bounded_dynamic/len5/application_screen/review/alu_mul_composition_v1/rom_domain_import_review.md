# Supplemental external-ROM importer review

Read-only review of `rom_domain_import.py` at SHA256
`8de4a3fd39bbffe97a2b0b0eaa87b4b740001dd5240ad0cc56dbc2bbcf3cd38a`
found no concrete soundness blocker. The inspected source is snapshotted here.

The validator binds the exact generated harness and native core JSON, ROM image,
port table, and concluded domain; reconstructs the checker using the frozen
extractor; checks positive source, JSON/SMT, solver-command and log hashes; requires
the base proof and successful temporal induction; verifies three assertions, one
assumption, no state initialization, and no unresolved X/Z cell connections; and
replays a whitelisted small model export to identical JSON and SMT. It does not run
a new solver query. The extractor retains the original synchronous pipeline reset
and introduces only the original initial-reset premise. The proof includes raw
payload bits on fault responses under the reset-qualified validity guard.

The negative controls are not revalidated by this importer. They are diagnostic
evidence; the source-bound positive unbounded theorem establishes applicability.
One minor provenance limitation was reported to the owner: packaged copies of the
positive base/induction logs are compared during import but are not separately in
the post-query dependency map. The original authoritative logs are included, so
their later changes invalidate the query; editing only an unused duplicate would
not. The owner deferred adding those duplicate paths until the active source-hash-
bound query finishes. No running source was changed for this review.
