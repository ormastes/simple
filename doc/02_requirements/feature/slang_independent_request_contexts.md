# Slang independent request-context requirements

Date: 2026-09-08. Status: selected S3 ownership contract, refined by Astra.

- REQ-001: Keep one resident model and admit a separately bounded number of requests.
- REQ-002: Each request owns its llama context, sampler, prompt/output buffers,
  tokens, prefill position, lifecycle state, and optional immutable-prefix lease.
- REQ-003: Address requests only through positive generation-tagged opaque handles.
- REQ-004: Reject stale, invalid, closed, exhausted, or prior-model handles.
- REQ-005: Count the legacy compatibility request against the request limit.
- REQ-006: A prefix match pins its immutable snapshot until request completion,
  cancellation, failure, or close releases the lease exactly once.
- REQ-007: Eviction ignores pinned entries; admission skips caching when pins
  prevent fit, while generation remains valid.
- REQ-008: Limit shrinking is atomic and rejected if live leases prevent the bound.
- REQ-009: Model unload rejects while requests are active; it must never unload
  a library after native teardown reports busy or failure.
- REQ-010: Cancellation is cooperative between native calls and releases owned
  resources; it does not claim interruption inside `llama_decode`.
- REQ-011: Resolve the entire optional S3 ABI group atomically. A partial group
  falls back to S2 and cannot advertise independent contexts.
- REQ-012: Preserve existing S1/S2 exports as wrappers around the compatibility request.
- REQ-013: Remain serial-owner executed. Do not advertise simultaneous threads,
  paged attention/KV, physical page sharing, COW tails, batching, spill, or transport.
