# SECURITY: PASETO v4 tampered token signature is accepted instead of rejected

- **Date:** 2026-07-20
- **Area:** PASETO v4 implementation exercised via
  `test/unit/lib/crypto/paseto_v4_kat_spec.spl`
- **Severity:** critical — this is an authentication-bypass-shaped defect
  (a tampered token is not being rejected). No exploitability/impact
  analysis was performed in this triage pass; that judgment is out of scope
  here and should not be assumed either way pending investigation.
- **Status:** RESOLVED (2026-09-12) — root cause was NOT signature verification; see "Root cause 2026-09-12" at the end of this file

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

## Root cause 2026-09-12 — TWO independent defects, neither in signature verification

Binary: `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` sha256 `3d120a6f`

RED: `paseto_v4_kat_spec` 14 examples, 8 passed, **6 failed** (the record says 1 of
14; it has been worse than reported for some time). `paseto_v4_b64url_decode_roundtrip_spec`
2 examples, 0 passed, 2 failed.

**Defect 1 — every v4 decrypt/verify aborted before reaching the MAC or signature.**
Five of the six failures reported `semantic: variable 'idx3' not found`.
`_p4_b64u_decode` (`src/os/crypto/paseto.spl:90`) declared

```
if i + 2 < clean_len:
    val idx3 = _p4_b64u_char_index(...)   # branch-local
if i + 3 < clean_len:
    val byte3 = (((idx3 & 3) << 6) | idx4) & 0xFF   # reads it from a SIBLING branch
```

so decoding any full 4-character base64url group raised an unresolved-variable
error. Every `v4.local` decrypt and `v4.public` verify goes through that decoder,
so all of them aborted — including the two tamper-rejection examples, whose
"rejected?" helpers report `false`/`true` purely from the match arm and cannot
distinguish "signature invalid" from "the decoder blew up". Encryption and signing
never call the decoder, which is why the byte-exact KAT encrypt/sign groups passed
and hid this. Fix: hoist `idx3` to the loop scope (`i + 3 < clean_len` implies
`i + 2 < clean_len`, so it is always assigned before the sibling branch reads it).

**Defect 2 — the v4.public tamper test never tampered.** `_tampered_public_ok`
built its "tampered" token as `good.substring(0, 15) + "X" + good.substring(16, …)`,
and character 15 of that token **is already `X`** (`…v4.public.eyJkYXRhIj…`), so the
"tampered" token was byte-identical to the valid one. The example was asserting that
a VALID token fails to verify; verification correctly returned "valid", which is the
`expected true to equal false` in the original report. This is a test defect, not an
authentication bypass — `_tampered_local_ok` (which flips a byte that really differs)
passes. The helper now picks a replacement character that differs from the one it
replaces, and returns "accepted" if the tamper changed nothing, so a future no-op
tamper fails instead of passing vacuously.

GREEN: `paseto_v4_kat_spec` 14/14 (both test trees), `paseto_v4_b64url_decode_roundtrip_spec`
2/2, new `paseto_v4_b64url_decode_scope_spec` 5/5 (0/5 before the fix).

- Status: RESOLVED (2026-09-12) — commit "fix(crypto): hoist idx3 out of the branch that never reaches its reader", spec test/01_unit/os/crypto/paseto_v4_b64url_decode_scope_spec.spl
