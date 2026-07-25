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
