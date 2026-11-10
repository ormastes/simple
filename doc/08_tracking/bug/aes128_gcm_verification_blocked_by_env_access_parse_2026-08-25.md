# AES-128-GCM verification blocked by hosted environment parse
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Date:** 2026-08-25  
**Status:** Open, unrelated blocker

The repository's nominal production path
`bin/release/x86_64-unknown-linux-gnu/simple` identifies itself as a Rust-built
bootstrap seed. The single attempted AES-128-GCM interpreter verification:

```text
SIMPLE_LIB=src bin/release/x86_64-unknown-linux-gnu/simple test
test/01_unit/lib/crypto/aes128_gcm_nist_vectors_spec.spl --mode=interpreter
```

stopped in approximately 0.2 seconds before loading the requested spec:

```text
src/app/io/env_access_host.spl: function arguments: expected Comma, found Pub
```

This does not provide pass or fail evidence for AES-128-GCM. The focused
static SFFI/extent/performance ratchet passes, but executable NIST-vector and
invalid-extent verification remains blocked until a pure-Simple production
binary can parse the current hosted environment sources.


## 2026-11-10 status — SUPERSEDED (P3 library lane, work/p3-lib-20261110)

The named blocker is gone: the env_access_host.spl parse failure was fixed by
`a8a32ebccad` (tracked in
origin_main_not_test_runnable_env_access_host_parse_2026-08-25.md, "Status: the
original defect is FIXED"), which is an ancestor of this lane's base
(`git merge-base --is-ancestor a8a32ebccad HEAD` passes on
origin/release/1.0.0). Re-running the recorded command on this lane's tree with
the deployed seed no longer produces the parse error; the run proceeds to
semantic/runtime stages and stops on a different, Windows-seed-specific gap:
`error: semantic: unknown extern function: GetProcessHeap` (declared in
`src/lib/nogc_sync_mut/io/windows_process_owner_abi.spl`, absent from the
deployed seed's dispatch — a seed/runtime registration gap, not a src/lib
defect). Executable NIST-vector verification therefore remains host-limited on
Windows seeds; the env-parse premise of this record is stale.
