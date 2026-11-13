# AES-128-GCM verification blocked by hosted environment parse
## FIXED 2026-11-13 — see "Resolution 2026-11-13" at the end
## (historical) Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Date:** 2026-08-25  
**Status:** SUPERSEDED, unrelated blocker

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

## 2026-11-11 status — SUPERSEDED (P3-essential library lane, work/p3-lib3-20261111)

Re-verified with this lane's refreshed seed (bin/simple.exe, build-commit
0791c2b7f4a7, 2026-11-11). Seed-smoke: `SIMPLE_LIB=src
SIMPLE_BINARY=$PWD/bin/simple.exe $PWD/bin/simple.exe test
test/fixtures/doctest/green.md --mode=interpreter --no-cache` runs the
full doctest to `PASS (1 passed, 0 skipped, 83ms)`, rc=0 — the
`env_access_host.spl` parse failure (fixed in `a8a32ebccad`, ancestor of
this base) is gone, and unlike the 2026-11-10 lane's run there is no
Windows-seed extern stop on this seed. Env-facade lens: the historical
blocker was a parse-level defect, not a raw env read; no direct-env
violation observed in the load path. Executable AES-128-GCM NIST-vector
verification remains a separate coverage question for the crypto owner,
but this record's premise is stale.

## Addendum 2026-11-13 — lane p3-comp1 (worktree p3comp1-wt, branch work/p3-compiler-p1-20261113)

Concurs: SUPERSEDED stands (recorded 2026-09-16 bookkeeping review; the parse
blocker was an unrelated env-access-host issue). No new evidence this lane.

## Resolution 2026-11-13 — FIXED (lane work/p3-aesgcm-20261113)

With the parse blocker gone the NIST-vector spec ran and exposed a real
fail-open defect: `aes128_gcm_decrypt` in `src/os/crypto/aes128_gcm.spl`
(the module the spec imports as `os.crypto.aes128_gcm`, not a `src/lib`
file) validated no input length. A short key, nonce or tag was read through
`rt_bytes_u8_at` past its end, and decryption surfaced only as a generic
"authentication tag mismatch" (or proceeded on degenerate bytes).

Red (base `f9411a43849`, seed-fix aarch64, interpreter):
`aes128_gcm_nist_vectors_spec.spl` executed=15 passed=12 failed=3 — short
tag, short nonce **and** short key rejection examples.

Fix: three length guards at the top of decrypt, before any input byte is
read: key 16 bytes, nonce 12 bytes, tag 16 bytes, each returning
`Aes128GcmResult.Err`. The 16-byte OR-accumulate constant-time tag compare is
unchanged; lengths are public, so the early return leaks nothing secret.

NIST rule implemented: a restricted SP 800-38D profile. IV: 96 bits only
(SP 800-38D 5.2.1.1 recommends restricting IV support to 96 bits; this module
only implements the 96-bit J0 = IV || 0^31 || 1 construction). Tag: t = 128
only (one of the 5.2.1.2 permitted lengths {128,120,112,104,96}, plus 64/32
for special applications — the shorter ones are deliberately not supported).
Per SP 800-38D 7.2 step 1 (authenticated decryption), an unsupported IV
length or len(T) != t returns FAIL, which is what the guards do.

Green: `aes128_gcm_nist_vectors_spec.spl` executed=15 passed=15 failed=0.
Regression set, before -> after, identical: aes_gcm_common_kat 5/5,
aes256_gcm_nist_vectors 12/12, aes192_gcm_kat 5/5, aes_gcm_rfc_vectors 11/11,
os_crypto_native_kat_fixture 1/1, record13_checked_seal 17/17,
ssh_cipher_packet_assembly 1/1, typed/aead 12/12, aes128_ccm_rfc3610 12/12;
tls12_record 0/2 pre-existing on base and unchanged. Callers of this module
(tls_common_hooks, tls13 record13, sshd ssh_cipher_live) already pass 12-byte
nonces and 16-byte tags; none branches on the old message text for malformed
input.

Remaining (not in scope here, recorded as open gaps):
- `aes128_gcm_encrypt` still does no length validation and returns bare
  `[u8]`, so it cannot report an error without a signature change.
- Sibling copies without the guards: `src/os/services/nvfs/core/crypto/aes128_gcm.spl`
  (the copy nvfs actually calls) and `src/lib/nogc_async_mut_noalloc/tls/aes128_gcm.spl`;
  `src/os/crypto/aes256_gcm.spl` also has no length checks.
