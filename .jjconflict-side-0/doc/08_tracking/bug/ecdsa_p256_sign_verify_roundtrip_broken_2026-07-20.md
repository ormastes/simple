# ECDSA P-256: fresh sign+verify round-trip fails; NIST CAVP vector fails verify

- **Date:** 2026-07-20
- **Area:** ECDSA-P256 implementation exercised via
  `test/unit/lib/crypto/ecdsa_p256_spec.spl`
- **Severity:** high (verify rejects a signature this repo's own sign just
  produced — a basic round-trip break, not an edge case).
- **Status:** OPEN. **Do not touch the NIST CAVP vector.**

## Symptom

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 bin/release/x86_64-unknown-linux-gnu/simple \
  test test/unit/lib/crypto/ecdsa_p256_spec.spl --no-session-daemon
```

```
ECDSA-P256-SHA-256 round-trip sign + verify
✓ sign returns a 64-byte signature
✗ signs and verifies an empty message
    expected false to equal true
✗ signs and verifies a short ASCII message
  (6 examples, 2 failures)

ECDSA-P256-SHA-256 NIST CAVP SigVer
✗ NIST CAVP P-256 SHA-256 vector verifies (Result = P)
```

`sign` itself produces a correctly-sized (64-byte) signature, but `verify`
called on that same fresh signature returns `false` instead of `true`.

## Root-cause hypothesis

Unlike the P-384 case (`doc/08_tracking/bug/ecc_p384_p521_sign_verify_broken_2026-07-20.md`,
where `sign` itself is broken — 0-byte output), P-256 `sign` produces
correctly-shaped output, but `verify` rejects it. Combined with the NIST
CAVP vector (verifying an externally-supplied, known-correct signature)
also failing, this points at a bug in P-256 `verify` specifically (rather
than in `sign`) — e.g. in the signature-verification equation
(`u1*G + u2*Q` recomputation), scalar/point encoding mismatch between what
`sign` emits and what `verify` expects, or a hash-to-scalar conversion bug.
Not further localized within the P-256 implementation in this triage pass.

Given P-384's CAVP verify and P-521's CAVP verify also fail (see the
sibling doc above), there is a plausible shared ECDSA-verify-core root
across all three curves — flagged as a hypothesis for a follow-up
investigation to confirm or rule out, not asserted here.

## What NOT to do

Do not touch the NIST CAVP P-256 vector.

## Affected specs

- `test/unit/lib/crypto/ecdsa_p256_spec.spl` (3 failures: 2 round-trip, 1
  CAVP verify)
