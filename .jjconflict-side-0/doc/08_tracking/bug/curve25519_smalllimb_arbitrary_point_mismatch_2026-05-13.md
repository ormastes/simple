# Curve25519 small-limb arbitrary-point mismatch

Date: 2026-05-13
Status: RESOLVED
Severity: Was a production blocker for X25519-based TLS/SSH key exchange

## Evidence

After removing the dead kernel-log dependency from
`src/os/crypto/curve25519_smalllimb.spl`, the existing RFC 7748 spec executes
instead of failing early on `log_info`.

Command:

```bash
bin/simple test test/01_unit/lib/crypto/curve25519_rfc7748_spec.spl --mode=interpreter
```

Original observed result: 3 examples passed and 4 failed. The failures were:

- RFC 7748 single scalar-mult TV1
- RFC 7748 single scalar-mult TV2
- Alice computes shared secret from Bob public key
- Bob computes shared secret from Alice public key

Base-point public-key examples pass, so the current failure appears specific to
arbitrary peer u-coordinate multiplication, not all scalar multiplication.

## Root Cause

`src/os/crypto/curve25519_smalllimb.spl::_x25519_fe_from_bytes` used the signed
ref10 carry schedule while the small-limb implementation stores limbs as `u64`.
For arbitrary u-coordinates, decode produced negative intermediate limbs in the
reference algorithm; under `u64` those subtracts underflowed before the ladder.

The fix replaced decode with direct nonnegative bit slicing for the 26/25-bit
radix layout and kept the no-shift conversion style required by the current
bootstrap.

## Impact

The RFC 7748 arbitrary-point vectors now pass. TLS server live accept still has
other production blockers, but this specific X25519 backend blocker is closed.

## Verification

Passing commands:

```bash
bin/simple test test/01_unit/lib/crypto/curve25519_smalllimb_probe_spec.spl --mode=interpreter
bin/simple test test/01_unit/lib/crypto/curve25519_rfc7748_spec.spl --mode=interpreter
bin/simple test test/01_unit/os/tls13/server_accept_spec.spl --mode=interpreter
```

Re-verified 2026-05-29: all 7 RFC 7748 test vectors pass (including the 4
arbitrary-point vectors that were previously failing), and the smalllimb probe
spec passes. Implementation at `src/os/crypto/curve25519_smalllimb.spl` uses
correct nonnegative bit-slicing (`_load4` + mask with `MASK26`/`MASK25` via
unsigned division shift) — no signed carry-schedule underflow.
