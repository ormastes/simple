<!-- codex-design -->
# Secure Pure-Simple Servers — Non-Functional Requirements

Status: Accepted. These constraints refine REQ-001..REQ-014.

- **NFR-001 Fail closed:** Invalid policy, credentials, framing, capacity,
  protocol state, or TLS material rejects before application dispatch or
  mutation. Evidence: negative SSpec scenarios mapped to REQ-002/003/005/008.
- **NFR-002 Bounded resources:** Limits for connections, messages, request
  line, headers, body, reads, response bytes, batch items, and range items are
  positive, explicit, and exercised at boundary and boundary+1. Evidence:
  focused system scenarios for REQ-002/004/008.
- **NFR-003 Confidentiality:** Secrets never appear in responses, diagnostics,
  logs, or retained captures. Production traffic is not accepted as secure
  until an owned encrypted-stream transport exists. Evidence: source scan,
  negative captures, and TLS integration scenario for REQ-003/005.
- **NFR-004 Integrity:** Failed authentication, authorization, overflow,
  conflict, or persistence leaves no partial application. Evidence: reopen
  from disk and independent-reader oracles for REQ-005..008.
- **NFR-005 Determinism:** Range ordering, batch result ordering, rejection
  classes, conflict behavior, and commit retry results are stable across
  runs/reopen. Evidence: exact ordered assertions for REQ-007/008.
- **NFR-006 Availability and cleanup:** A rejected or disconnected client
  releases its transport/session slot; bounded backpressure rejects excess
  work and explicit shutdown releases the listener. Evidence: lifecycle SSpec
  and post-shutdown bind probe for REQ-004.
- **NFR-007 Hot paths:** Startup performs no full-tree scan; accepted web and DB
  requests perform no subprocess launch or repeated filesystem discovery.
  Static policy/configuration is validated once and retained. Evidence:
  dependency/direct-runtime audit and implementation review.
- **NFR-008 Performance budgets:** On the repository fixture with a healthy
  Stage-4 CLI, warm startup to listening is <=250 ms, p95 loopback request
  latency is <=25 ms for a single-row/route request, and max RSS is <=128 MiB
  at configured capacity. Record fixture, sample count, wall time, p95, and
  max RSS; an unavailable healthy CLI yields WARN, never PASS.
- **NFR-009 Observability:** Debug diagnostics expose validation/rejection
  categories, active/accepted/rejected connection counts, request/message
  counts, commit/retry/conflict counts, and timing without credential or
  request-body disclosure.
- **NFR-010 Pure-Simple ownership:** Production protocol behavior remains in
  `.spl` modules and accesses environment/process/socket/file facilities only
  through owned facades. Evidence: direct-runtime and dependency gates.
- **NFR-011 Evidence quality:** Each criterion is verified once per session,
  no placeholder assertion or stub is credited, and no criterion exceeds
  three verify/fix cycles.

## Blocking interpretation

The current certificate/key checks satisfy only startup rejection. GAP-TLS-3
prevents confidentiality, TLS request latency, and encrypted production-flow
evidence from satisfying NFR-003/NFR-008.
