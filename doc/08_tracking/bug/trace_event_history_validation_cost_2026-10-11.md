# Trace event history validation requires an owner generation index

Status: open; source-level cost identified, runtime measurements pending.
Requirements: REQ-TRC-010, REQ-TRC-017, REQ-TRC-018.

The strict event-storage decoder validates the full existing table on append,
query and plan ordering checks. This protects against malformed replacement
rows and decoded identity collisions across legacy and encoded storage.
The previous cache had no mutation-generation binding while the underlying
table remains publicly replaceable, so it could reuse stale identity facts.

For F file batches and H historical events, repeated appends can inspect
O(F * H) records. No latency or memory budget is qualified by this code.

Implement an owner mutation generation, bind decoded identity/scope indexes
to that generation, invalidate on every supported table replacement and
retain strict cold-rebuild equivalence. Keep row encoding validation before
mutation. Measure large-history batch appends and reload/replay fixtures on
the admitted Phase 3 runtime before closing this issue or claiming NFR PASS.
