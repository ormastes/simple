# ECDSA P-384/P-521: sign returns 0-byte signature, NIST CAVP verify fails on both curves

- **Date:** 2026-07-20
- **Area:** ECDSA-P384/P521 implementation exercised via
  `test/unit/lib/crypto/ecc_p384_p521_kat_spec.spl`
- **Severity:** high (sign is non-functional for P-384; verify fails NIST
  CAVP vectors for both curves).
- **Status:** OPEN. **Do not touch the NIST CAVP vectors.**

## Symptom

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 bin/release/x86_64-unknown-linux-gnu/simple \
  test test/unit/lib/crypto/ecc_p384_p521_kat_spec.spl --no-session-daemon
```

```
ECDSA-P-384 NIST CAVP SigVer
✗ NIST CAVP P-384 SHA-384 vector verifies (Result = P)
  (5 examples, 1 failure)

ECDSA-P-384 round-trip sign + verify
✗ sign returns a 96-byte signature
    expected 0 to equal 96
✗ signs and verifies an empty message
    expected false to equal true
✗ signs and verifies a short ASCII message
    expected false to equal true
✗ RFC 6979 is deterministic: same message produces same signature
  (7 examples, 4 failures)

ECDSA-P-384 SSH mpint helper
✗ fixed96_to_ssh_mpint_pair returns non-empty output for 96-byte sig
  (2 examples, 1 failure)

ECDSA-P-521 NIST CAVP SigVer
✗ NIST CAVP P-521 SHA-512 vector verifies (Result = P)
✓ NIST CAVP P-521 vector is rejected when signature r-byte is flipped
✓ NIST CAVP P-521 vector is rejected when signature s-byte is flipped
```

7 failures across 4 describe blocks (itemized above); the P-521
negative-path tamper-rejection checks pass even though the positive
CAVP-vector check fails.

## Root-cause hypothesis

For **P-384**, `sign` returns a signature of length **0** instead of 96
bytes (`expected 0 to equal 96`) — sign is not producing output at all, not
merely producing a wrong value. Every downstream P-384 check that depends
on a real signature (empty-message round-trip, short-ASCII round-trip,
RFC 6979 determinism, the SSH mpint helper) cascades from this single
broken `sign`. This is very likely ONE root cause for the entire P-384
"round-trip" and "SSH mpint helper" describe blocks (5 of the 5 total
failures), separate from the P-384 CAVP `verify`-only failure and the
P-521 CAVP `verify`-only failure, which exercise `verify` against an
externally-supplied signature and don't depend on this repo's `sign`.

For **P-521**, `verify` rejects the genuine CAVP vector's signature (while
correctly rejecting corrupted r/s bytes) — suggesting `verify`'s underlying
signature math (or the CAVP vector's message/hash digestion) has a bug
independent of the P-384 `sign` breakage. Given P-384's CAVP `verify` also
fails, there may be a shared P-384/P-521 ECDSA-verify-core root distinct
from the P-384-only `sign` breakage — this needs a source-owner follow-up to
confirm or separate further; not conclusively determined in this triage
pass.

## What NOT to do

Do not touch any NIST CAVP vector bytes, nor the 96-byte expected signature
length.

## Affected specs

- `test/unit/lib/crypto/ecc_p384_p521_kat_spec.spl` (all 5 reported
  failures: P-384 CAVP verify, P-384 sign+round-trip ×4, P-384 SSH mpint
  helper, P-521 CAVP verify)
