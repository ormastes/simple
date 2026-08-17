## Triage 2026-08-17 — OPEN, design work not re-verifiable by inspection

Not stale: the 2026-08-14 partial mitigation (`ParentCommitFrameInboxV1`,
`ParentCommitPipedProcessSessionV1`) covers the bounded-session half only. The
remaining acceptance rows — cryptographic wire-hash authentication (FNV-1a is
not authentication), PID-reuse/namespace simulation, and exec-isolated child
tests — are unimplemented. Left OPEN; out of scope for a bug-doc verification
pass because it needs the admitted crypto wire-hash contract first.

# Process transfer session and replay identity

Status: open

The native transfer allocator packs the low 31 PID bits and a 32-bit local
sequence into a positive `i64` RegionId. This prevents duplicated atomic-counter
collisions for one live same-host parent/child pair, including an exec child.
It does not provide global uniqueness across PID namespaces, PID reuse, stale
frame replay, or process restarts.

The bounded process-frame decoder currently verifies route, destination,
length, and an FNV-1a corruption checksum. Production transport must additionally
bind each request/result to a parent-issued process-session identity and reject
unexpected or replayed `(region_id, generation)` pairs. Authentication for
remote or hostile transports requires the admitted cryptographic wire-hash
contract; FNV-1a is not authentication.

Acceptance evidence:

- production spawn/piped adapter issues a fresh session identity;
- response decode requires the expected session and generation;
- replay of an already accepted frame is rejected;
- PID reuse and namespace simulation cannot authorize a stale frame;
- cancellation revokes outstanding ownership/session tokens;
- tests use an exec-isolated child and bounded timeout/cleanup.

## 2026-08-14 partial mitigation

`ParentCommitFrameInboxV1` can now bind a finite inbox to an expected
generation, reject another generation, and reject repeated region IDs for the
lifetime of that bounded session. `ParentCommitPipedProcessSessionV1` refuses
an inbox/session generation mismatch, owns one piped handle, and records an
idempotent explicit close result.

The bug remains open because the generation is caller-selected rather than
issued by a freshness authority; PID reuse/namespace simulation, cancellation
revocation, natural-exit reap, and close-wakeup are not covered. The real-child
system spec also lacks an admitted Stage 4 verdict.

Resume after the deployed CLI passes `bin/release/simple test --help`:

```text
SIMPLE_LIB=src bin/release/simple test test/03_system/feature/language/parent_commit_piped_result_spec.spl --mode=native
```

Extend that scenario with parent-issued session identity, stale PID/session
replay, cancellation revocation, and bounded terminal cleanup before changing
`Status: open`.
