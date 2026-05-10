# W-SHA Done Note — NIST FIPS 180-4 + CAVP KATs for SHA-256 / SHA-512

**Wave:** 5
**Feature:** `crypto-pure-simple-port`
**Date:** 2026-04-25
**Branch:** `worktree-w-sha-kat`
**Commit:** `502fa6ec2cd4616b72d681c941f5f6490654e924`

## Deliverables landed

- `test/unit/os/crypto/sha256_nist_spec.spl` (84 LOC, 4 `it` blocks, 8 `expect` assertions)
- `test/unit/os/crypto/sha512_nist_spec.spl` (101 LOC, 4 `it` blocks, 8 `expect` assertions)
- `doc/08_tracking/bug/bug_sha512_rt_extern_unresolved_2026-04-25.md` (bug surfaced by SHA-512 KATs)

## KAT inventory (per file)

### sha256_nist_spec.spl — 4 KATs, 8 assertions, 4/4 PASS
1. FIPS 180-4 Appendix B.1 — `sha256("abc")` = `ba7816bf...20015ad`
2. FIPS 180-4 Appendix B.2 — `sha256("abcdbcde...nopq")` (56 bytes) = `248d6a61...19db06c1`
3. Wycheproof tcId 1 — `sha256("")` = `e3b0c442...7852b855`
4. Determinism — repeated call returns identical digest

### sha512_nist_spec.spl — 4 KATs, 8 assertions, 0/4 PASS (impl bug, see below)
1. FIPS 180-4 Appendix C.1 — `sha512("abc")` = `ddaf35a1...a54ca49f`
2. FIPS 180-4 Appendix C.2 — `sha512("abcdefgh...nopqrstu")` (112 bytes) = `8e959b75...874be909`
3. Wycheproof tcId 1 — `sha512("")` = `cf83e135...927da3e`
4. Determinism — repeated call returns identical digest

All expected digests independently cross-checked against GNU `sha256sum` /
`sha512sum`. 1M 'a' NIST monte-carlo KAT intentionally skipped (perf-prohibitive
under the interpreter; documented inline).

## Pass / Fail breakdown

| Spec | Examples | Failures | Status |
|------|----------|----------|--------|
| `sha256_nist_spec.spl` | 4 | 0 | GREEN |
| `sha512_nist_spec.spl` | 4 | 4 | RED — bug filed |

Total: 8 KATs, 16 assertions, 4 pass / 4 fail. The 4 SHA-512 failures
are not vector errors — the digests themselves match `sha512sum` — they
are caused by the public `sha512(...)` entry point calling an extern
`rt_sha512_hash` that is not registered with the interpreter's runtime
extern table.

## Bugs filed

- `doc/08_tracking/bug/bug_sha512_rt_extern_unresolved_2026-04-25.md`
  — `unknown extern function: rt_sha512_hash` blocks every hosted call
  to `os.crypto.sha512.sha512`. Read-only on impl per W-SHA scope —
  three suggested fix paths recorded in the bug doc.

## Deliberate-fail proof (SHA-256 spec, runner credibility check)

Per `feedback_compile_mode_false_greens.md`: `bin/simple test` is
unreliable; `bin/simple <spec>` direct is the trustworthy path, and
each new crypto KAT must be probed with a known-bad assertion.

```
# Probe: change first byte of expected from 0xba to 0xbb
$ md5sum test/unit/os/crypto/sha256_nist_spec.spl
fa251c2c02c1079822cd99a32ba680cd  test/unit/os/crypto/sha256_nist_spec.spl
$ bin/simple test/unit/os/crypto/sha256_nist_spec.spl
SHA-256 NIST FIPS 180-4 KATs
  ✗ FIPS 180-4 worked example: 'abc' produces ba7816bf...20015ad
    expected false to equal true
  ✓ FIPS 180-4 longer message ...
  ✓ Wycheproof tcId 1 ...
  ✓ determinism ...
4 examples, 1 failure

# Revert and re-verify md5
$ md5sum test/unit/os/crypto/sha256_nist_spec.spl
8080eeb0411fec894d3d9d0200b60bbc  test/unit/os/crypto/sha256_nist_spec.spl
$ bin/simple test/unit/os/crypto/sha256_nist_spec.spl
SHA-256 NIST FIPS 180-4 KATs
  ✓ ... (all 4)
4 examples, 0 failures
```

Probe transitions RED → GREEN as expected. Runner is executing
assertions truthfully; the SHA-256 4/4 green is real; the SHA-512 4/4
red is real (and is a runtime-wiring bug, not a vector bug).

## Scope discipline

- New test files only under `test/unit/os/crypto/sha*` (per task scope).
- One bug doc under `doc/08_tracking/bug/` (allowed by task spec when
  impl bug is surfaced).
- No source file under `src/os/crypto/` modified.
- 1M 'a' KAT documented as deliberately skipped, not silently dropped.

## Runner used

`bin/simple <abs-path-to-spec>` direct invocation (not `bin/simple test`)
per `feedback_compile_mode_false_greens.md` 2026-04-25 update.

## Worktree persistence

```
git worktree add --detach /tmp/w-sha-kat HEAD
# (copy new files in)
git -C /tmp/w-sha-kat add test/unit/os/crypto/sha*_spec.spl \
                         doc/08_tracking/bug/bug_sha512_rt_extern_unresolved_2026-04-25.md
git -C /tmp/w-sha-kat commit -m "test(crypto/sha): NIST FIPS 180-4 + CAVP KATs for sha256 + sha512 (W-SHA)"
git -C /tmp/w-sha-kat update-ref refs/heads/worktree-w-sha-kat HEAD
# -> refs/heads/worktree-w-sha-kat = 502fa6ec2cd4616b72d681c941f5f6490654e924
```
