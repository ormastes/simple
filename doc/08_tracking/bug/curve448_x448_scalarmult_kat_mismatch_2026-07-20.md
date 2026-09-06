# Curve448 (X448) scalar-mult and ECDH KAT mismatches across all RFC 7748 vectors

- **Date:** 2026-07-20
- **Area:** Curve448/X448 implementation exercised via
  `test/unit/lib/crypto/curve448_rfc7748_kat_spec.spl`
- **Severity:** high (every KAT vector in the file mismatches — near-total
  break, not an edge case).
- **Status:** OPEN. **Do not touch the expected vectors** — RFC 7748 §5.2/§6.2
  values are canonical.

## Symptom

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 bin/release/x86_64-unknown-linux-gnu/simple \
  test test/unit/lib/crypto/curve448_rfc7748_kat_spec.spl --no-session-daemon
```

```
✗ TV1: scalar 3d262fdd... × u 06fce640... → ce3e4ff9...
✗ TV2: scalar 203d4944... × u 0fbcc2f9... → 884a0257...
✗ after 1 iteration from BASE_POINT: 3f482c8a...
✗ Alice public key: x448_keygen(alice_priv)[1] == alice_pub
✗ Bob public key: x448_keygen(bob_priv)[1] == bob_pub
✗ Alice computes shared secret: x448_dh(alice_priv, bob_pub) == shared
✗ Bob computes shared secret: x448_dh(bob_priv, alice_pub) == shared
```

Every scalar-mult and ECDH example in the file fails (single-scalar-mult TV1
and TV2, the 1-iteration BASE_POINT test, and all 4 §6.2 ECDH round-trip
checks) — the failing byte arrays bear no partial resemblance to the
expected ones (unlike, e.g., the AES-256-CTR bug where a prefix matched).

## Root-cause hypothesis

Total, not partial, mismatch across every vector (single scalar-mult,
iterated scalar-mult, and full ECDH key exchange) strongly suggests a
fundamental defect in the Curve448 field arithmetic or the core X448 ladder
(e.g. `x448_keygen`/`x448_dh`'s underlying scalar-mult routine) rather than
an edge case in one code path — since ECDH failing is a direct consequence
of `x448_keygen` (itself just scalar-mult against the base point) already
being wrong. Not further localized within the field-arithmetic
implementation in this triage pass; needs a from-scratch verification of
the Curve448 field reduction / Montgomery-ladder implementation against a
reference.

## What NOT to do

Do not touch any of the RFC 7748 §5.2/§6.2 expected byte values.

## Affected specs

- `test/unit/lib/crypto/curve448_rfc7748_kat_spec.spl` (all scalar-mult and
  ECDH examples fail)
