## Production integration 2026-08-17 — source complete; executable evidence pending

Status: source-complete / focused pure-Simple execution pending

The missing host-side authority is now implemented in pure Simple. The V2
boundary authenticates the complete canonical V1 wire plus session ID and
generation with HMAC-SHA256 before the existing typed decoder and bounded
replay inbox can admit it. Parent-issued session IDs bind an authority epoch,
process namespace, child PID, and generation; PID reuse cannot make a stale
tag valid in a replacement namespace or parent epoch. Cancellation revokes the
inbox and destroys accepted-but-uncommitted frames.

Focused regression evidence is
`test/01_unit/lib/nogc_async_mut/parent_commit_authenticated_session_spec.spl`:
wire mutation, wrong-key authentication, exact replay, PID/namespace reuse,
parent restart, and cancellation all fail closed.

`parent_commit_piped_process.spl` now integrates that authority into the real
process reader. `SPRF2` carries a fixed-width HMAC beside the canonical `SPRF1`
frame; authentication runs before generation/replay admission; spawn derives
the parent-issued identity; and cancellation revokes the reader's owned inbox.
The V1 constructor remains only as the explicit compatibility surface.

The exec-isolated scenario in `parent_commit_piped_result_spec.spl` emits a
wrong-session frame, one valid frame, and an exact replay before remaining
alive for cancellation. It asserts identity issuance, authentication-required
decode, wrong-session/replay rejection, and revocation. This worktree has no
deployed pure-Simple executable, so the scenario has not been executed here;
source completion is not a green runtime verdict.

Owned source:

- `src/lib/common/structural/transfer/process_frame_auth.spl`
- `src/lib/nogc_async_mut/parent_commit_authenticated_session.spl`
- `src/lib/nogc_async_mut/parent_commit_piped_process.spl`
- `test/03_system/feature/language/parent_commit_piped_result_spec.spl`

## Triage 2026-08-17 — superseded by source closure above

Not stale: the 2026-08-14 partial mitigation (`ParentCommitFrameInboxV1`,
`ParentCommitPipedProcessSessionV1`) covers the bounded-session half only. The
remaining acceptance rows — cryptographic wire-hash authentication (FNV-1a is
not authentication), PID-reuse/namespace simulation, and exec-isolated child
tests — are unimplemented. Left OPEN; out of scope for a bug-doc verification
pass because it needs the admitted crypto wire-hash contract first.

# Process transfer session and replay identity

Status: source-fixed

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

## 2026-08-17 — resume precondition re-checked, still blocked

This record's own resume gate is `bin/release/simple test --help`. Run today from
the repo root:

```
$ bin/release/simple test --help
error: refusing non-production Simple runtime: /mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple
EXIT=1
```

The deployed binary is the stale Rust seed and the wrapper fail-closes on it, so
`test/03_system/feature/language/parent_commit_piped_result_spec.spl --mode=native`
cannot be run, let alone extended. Blocked on a Stage 4 redeploy.

Independently of that, the largest remaining acceptance row is a DESIGN gap, not
a test gap: "cryptographic wire-hash authentication (FNV-1a is not
authentication)" needs the admitted crypto wire-hash contract to exist before a
spec can assert against it. Writing a spec now would pin FNV-1a, the very thing
this record says must be replaced. Status stays open; do not re-derive this
blocker on the next sweep.

## Re-triage 2026-08-17 (content-classified, m9a_tests lane)

**Verdict: LIVE — the FNV-1a identity is still the shipped mechanism.**

`src/lib/common/structural/transfer/process_frame_codec.spl` still derives
session identity from a non-cryptographic FNV-1a hash:

- line 23: `val PROCESS_TRANSFER_FNV1A_OFFSET: i64 = -3750763034362895579`
- line 24: `val PROCESS_TRANSFER_FNV1A_PRIME: i64 = 1099511628211`
- lines 74-78: `var hash = PROCESS_TRANSFER_FNV1A_OFFSET` ... `hash = hash * PROCESS_TRANSFER_FNV1A_PRIME`

No keyed MAC, no cryptographic wire-hash. This confirms the docs own
2026-08-14 note that the mitigation covered the bounded-session half only: the
crypto wire-hash, PID-reuse and exec-isolated rows remain unimplemented.

**DIAGNOSIS ONLY — not fixed here.** The fix is in `src/lib/**`, outside the
test lanes file scope.
