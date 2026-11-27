# Nullable native Linux collection receipts

Status: **NOT_RUN**. Authored manual; no admitted runtime or doc generator was executed.

Source: `test/01_unit/lib/nogc_sync_mut/io/linux_process_collection_nullable_v2_spec.spl`.

REQ-COLLECTION-NULL-001: a missing allocation must produce a typed receipt-unavailable error, never terminal, absent-workload or cleanup proof.

REQ-COLLECTION-NULL-002: present receipts retain the existing native status, layout, memory bounds, tree-reap validation and observed fields.

| Scenario | Expected result |
|---|---|
| Absent native receipt | Error explicitly retains the lease |
| Empty or truncated present receipt | Layout error |
| Unsupported or invalid native status | Original numeric owner error, distinct from missing allocation |
| Terminal receipt without complete leader/tree reap | Rejected |
| Current memory exceeds peak | Rejected |
| Complete observed terminal receipt | Preserve exit code, timeout, cancellation, tree and memory facts |
| Present nonterminal receipt | Preserve nonterminal state and active charge |

These seven pure decoder cases exercise the same production helper used by poll, collection and collected-stream recovery. They do not simulate native allocation, execute cleanup, or establish native ownership/completion. Native allocation-failure qualification and broker retry integration remain NOT_RUN.
