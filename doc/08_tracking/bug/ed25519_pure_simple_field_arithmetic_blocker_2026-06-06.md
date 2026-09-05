# Ed25519 Pure Simple Field Arithmetic Blocker (2026-06-06)

Status: Resolved for the pure Simple Ed25519 path. Rust/SFFI seed/runtime signing can be checked after this 

## Status

Resolved for the pure Simple Ed25519 path. Rust/SFFI seed/runtime signing can be checked after this fix, but the root blocker was in pure Simple field arithmetic.

## Evidence

- `bin/simple test test/01_unit/lib/crypto/ed25519_field_ops_spec.spl --clean --json`
  reports `5 passed / 0 failed`.
- `bin/simple test test/01_unit/lib/crypto/ed25519_rfc8032_spec.spl --clean --json`
  reports `15 passed / 0 failed`.
- `bin/simple test test/01_unit/lib/crypto/ed25519_ct_property_spec.spl --clean --json`
  reports `5 passed / 0 failed`.
- `fe_to_bytes(fe_one())` previously encoded as 32 zero bytes because
  `fe_to_bytes` called `_store_limb(buf: result, ...)` without receiving the
  modified buffer back from the helper.
- RFC 8032 SHA(abc) public key fixture in
  `test/01_unit/lib/crypto/ed25519_rfc8032_spec.spl` was corrected to the
  32-byte RFC value ending `...c35467ef2efd4d64ebf819683467e2bf`.

## Root Cause

`src/os/crypto/curve25519.spl` used a 5-limb `Fe25519` backend whose multiply,
square, and inversion paths depended on `u128` intermediates. The pure Simple
interpreter/runtime path did not preserve those intermediates reliably enough
for Ed25519 projective normalization. X25519 remained green because the public
X25519 API already routes through `curve25519_smalllimb.spl`, which avoids
these `u128` paths.

## Fixes Landed

- `fe_to_bytes` now receives each `_store_limb` result explicitly.
- `_fe_carry_wide` now propagates carries beyond `n1` after folding high bits.
- `fe_mul`, `fe_sq`, and `fe_invert` keep the public 5-limb `Fe25519` API but
  route through the interpreter-safe 10-limb small-field backend by direct limb
  conversion, not byte round-trips.
- `ed_point_add` now uses the standard extended Edwards add formula with
  `(Y-X)/(Y+X)`, `2*d*T1*T2`, and `2*Z1*Z2`.
- Added `test/01_unit/lib/crypto/ed25519_field_ops_spec.spl` covering:
  `fe_to_bytes(fe_one())`, `fe_sq` across the 64-bit boundary,
  `fe_mul(2, fe_invert(2))`, `ed_point_add(identity, B)`, and
  `ed_scalar_mul(1, B)`.

## Follow-Up

Re-check the Rust/SFFI Ed25519 wrapper and TLS/SSH positive-signature gates
against the now-correct pure Simple implementation.
