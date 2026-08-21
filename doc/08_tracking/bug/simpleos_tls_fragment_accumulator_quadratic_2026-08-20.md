# SimpleOS shared TLS fragment accumulator is quadratic

**Status:** IMPLEMENTED — admitted self-hosted runtime evidence pending
**Owner:** shared TLS application-record stream owner
**Found:** 2026-08-20

## Defect

The original `_append_bounded_v1` rebuilt the complete retained prefix on every
ingest. Adversarial one-byte fragmentation therefore performed O(n²) byte
copying before a record was framed.

The shared owner is one mutable `TlsApplicationRecordStreamV1` with a
fixed-capacity ring. `stream.ingest(...)` writes every accepted ingress byte
once, copies each complete wire record once into the authentication handoff,
and never coalesces an incomplete prefix. No buffer or stream crosses the API
by value. The byte capacity is the sole retention/admission bound, so a maximum
legal TLS record is accepted even when TCP delivers all 16,405 wire bytes
separately. Malformed framing, sequence exhaustion, and byte overflow fail
closed.

Complete frames create a pending generation-bound proposal. Logical head and
receive sequence remain unchanged until the caller authenticates every frame
and calls `stream.commit_authenticated(token, record_count)`. A second ingest
while pending is rejected; token/count mismatch or explicit
`reject_authentication(token)` makes the owner terminal, matching the callers'
close-and-drop failure policy.

Both HTTP and DBD consume this shared owner, so neither may claim production
TLS throughput or fragmentation-resilience performance while this record is
open. The corresponding SFTP accumulator has its own protocol-specific tracker.

## Evidence

- Implementation: `src/lib/common/net/tls_application_record_stream_v1.spl`
- Behavioral coverage:
  `test/01_unit/lib/common/net/tls_application_record_stream_spec.spl`
- The maximum-record one-byte fragmentation case observes exact cumulative
  work for N=16,405 bytes: N ring writes + (5N-10) bounded header probes + N
  record-handoff copies = 7N-10 = 114,825 operations.
- The byte ceiling is behaviorally exercised without source-text inspection.

## Remaining admission

Run the focused spec and retain representative latency/peak-RSS evidence with a
proven self-hosted binary. Rust-seed, unknown-provenance, or silent fallback
output does not close this release blocker.

## Runtime evidence 2026-08-21

Binary: `bin/release/x86_64-unknown-linux-gnu/simple` (Rust bootstrap seed —
it self-identifies as such). A proven self-hosted binary was NOT available:
a full bootstrap was running concurrently in this worktree, so the
self-hosted admission below is still outstanding.

- `bin/simple test test/01_unit/lib/common/net/tls_application_record_stream_spec.spl`
  -> `Results: 7 total, 7 passed, 0 failed` / `Duration: 11038ms` /
  `PASS test/01_unit/lib/common/net/tls_application_record_stream_spec.spl`.
- Source re-verified: `ingest` writes each admitted byte once at
  `write_offset = self.retained_length` into the fixed-capacity ring
  (`TLS_MAX_RX_BUFFER_LENGTH_V1`); `commit_authenticated` advances
  `retained_head` via `ring_index(pending_consumed)` rather than copying the
  remainder. No full-prefix rebuild remains, so per-fragment cost is
  O(fragment_len) and total ingest work is linear in admitted bytes.

**Caveat worth recording:** `bin/simple test` exited 0 on a run whose own
verdict line said `failed=1` (observed on the sibling SFTP spec). Exit status
alone is not a pass signal here — read the `Results:`/`SPEC FILE VERDICT`
line.

**Still open:** self-hosted-binary latency/peak-RSS evidence.
