# SECURITY: PASETO v4 tampered token signature is accepted instead of rejected

- **Date:** 2026-07-20
- **Area:** PASETO v4 implementation exercised via
  `test/unit/lib/crypto/paseto_v4_kat_spec.spl`
- **Severity:** critical — this is an authentication-bypass-shaped defect
  (a tampered token is not being rejected). No exploitability/impact
  analysis was performed in this triage pass; that judgment is out of scope
  here and should not be assumed either way pending investigation.
- **Status:** OPEN.

## Symptom

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 bin/release/x86_64-unknown-linux-gnu/simple \
  test test/unit/lib/crypto/paseto_v4_kat_spec.spl --no-session-daemon
```

```
✗ tampered token signature is rejected
    expected true to equal false
```

1 of 14 examples fails (13 pass, including other sign/verify round-trips in
the same file — this is not a total break of PASETO v4 signing).

## Root-cause hypothesis

The failing assertion's message ("expected true to equal false") indicates
the test computed `true` (tamper detected / signature invalid) where the
spec's own logic expects `false` for a *correctly functioning* rejection —
or equivalently, that the verify call returned "valid" for a token the test
had deliberately corrupted. Not further root-caused in this pass (would
require reading the exact `it` block body and the PASETO v4 sign/verify
implementation under `src/os/crypto/` or `src/lib/common/crypto/` to
determine whether the bug is in signature verification, in how the test
corrupts the token, or in how the boolean is interpreted) — flagging with
high severity given the security shape of the symptom rather than
delaying.

## What NOT to do

Do not weaken or invert this assertion to force green under any
circumstances — this is exactly the class of check the "never soften an
assertion" rule exists to protect.

## Affected specs

- `test/unit/lib/crypto/paseto_v4_kat_spec.spl` (1 of 14 examples)

## Re-triage 2026-08-17 (content-classified, m9a_tests lane)

**Verdict: ALREADY-FIXED CANDIDATE (high confidence). The doc was filed when
"the primary source module [was] unlocated"; it is located now, and both the
PASETO verify path and the Ed25519 primitive underneath it are real.**

### The module the doc could not find

`src/os/crypto/paseto.spl`. Its v4.public verify path does enforce the
signature — the check is present and its failure is fatal, not advisory:

```
683:    if not ed25519_verify(pk, m2, sig):
```

built on the PAE-encoded message the sign path produces (`603: val sig =
ed25519_sign(sk_seed, pk, m2)`), imported at line 27 from
`os.crypto.ed25519.{ed25519_sign, ed25519_keypair_from_seed, ed25519_verify}`.

### The primitive is a real RFC 8032 verifier, not a stub

`src/os/crypto/ed25519.spl:444` `fn ed25519_verify(public_key: [u8], message:
[u8], signature: [u8]) -> bool` implements the full §5.1.7 procedure, and every
step that can reject actually rejects:

- `455-458`: length gates — `signature.len() != 64` and `public_key.len() != 32` return false
- `472-473`: non-canonical S rejected (`_sc_is_geq_L(s_bytes)` -> false), backed by a real `_sc_sub_L` borrow check at `510-517`
- `480-493`: `k = SHA-512(R || A || M) mod L` over the actual message bytes
- `495-503`: the group equation `S*B == R + k*A`, compared in encoded form
- `519-528`: `_bytes_equal` is a constant-time OR-of-XOR compare, not `==` on a prefix

This is the opposite of the failure mode the session brief warns about (a JIT
fallback swallowing a completely missing P-256 implementation): there is
nothing here that returns `true` on a path that skipped verification. A
tampered token changes `m2`, which changes `k`, which breaks the group
equation.

### The specs assertions are correctly oriented

`test/unit/lib/crypto/paseto_v4_kat_spec.spl` asserts rejection, not
acceptance — `_tampered_local_ok()` (line 184) and `_tampered_public_ok()`
(line 219) each flip one byte of a good token
(`good.substring(0, 15) + "X" + good.substring(16, good.length())`) and the
examples at lines 281 and 333 `expect(...).to_equal(false)`.

### Residual risk found while reading (NOT the reported bug)

`ed25519_verify` calls `ed_point_decode(public_key)` and `ed_point_decode(r_bytes)`
at lines 476-477 and **does not check the result for a decode failure**, though
its own docstring at 450-451 says "reject if invalid". That is a robustness gap
on malformed-key input, not a signature-acceptance bug on a tampered token, and
`src/os/crypto/**` belongs to another lane this session — recorded here as a
DIAGNOSIS for that owner, not fixed.

### Not runtime-confirmed

`bin/simple test test/unit/lib/crypto/paseto_v4_kat_spec.spl --timeout 1200`
did not reach a `Results:` line before this batch closed (host load average
81-133; sibling runs in this batch were SIGTERMed at rc=143, which per the
session brief is UNVERIFIED rather than failed). **Do not close this P1 on the
content evidence alone** — re-run the KAT spec on a quiet host and quote the
`Results:` line first. Given the code above, the expected outcome is GREEN.
