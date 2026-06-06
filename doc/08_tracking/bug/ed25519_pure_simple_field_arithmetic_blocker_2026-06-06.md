# Ed25519 Pure Simple Field Arithmetic Blocker (2026-06-06)

## Status

Open. Pure Simple Ed25519 must be fixed before Rust/SFFI seed/runtime signing is treated as authoritative.

## Evidence

- `bin/simple test test/01_unit/lib/crypto/ed25519_rfc8032_spec.spl --clean --json`
  currently reports `3 passed / 12 failed` after exposing the nonzero field
  encoding path.
- `fe_to_bytes(fe_one())` previously encoded as 32 zero bytes because
  `fe_to_bytes` called `_store_limb(buf: result, ...)` without receiving the
  modified buffer back from the helper.
- `ed_point_encode(_ed25519_base_point())` now encodes the base point as
  `58 66 ... 66`, but `ed_scalar_mul([1, 0, ...], B)` still does not encode as
  `B`.
- `fe_mul(2, fe_invert(2))` still encodes as zero, and repeated `fe_sq` over
  powers of two loses the value once the intermediate crosses the 64-bit range.

## Current Root Cause

`src/os/crypto/curve25519.spl` still uses a 5-limb `Fe25519` backend whose
multiply, square, and inversion paths depend on `u128` intermediates. The pure
Simple interpreter/runtime path does not currently preserve those intermediates
reliably enough for Ed25519 projective normalization. X25519 remains green
because the public X25519 API routes through `curve25519_smalllimb.spl`, which
avoids these `u128` paths.

## Partial Fixes Landed

- `fe_to_bytes` now receives each `_store_limb` result explicitly.
- `_fe_carry_wide` now propagates carries beyond `n1` after folding high bits.
- `ed_point_add` now uses the standard extended Edwards add formula with
  `(Y-X)/(Y+X)`, `2*d*T1*T2`, and `2*Z1*Z2`.

## Next Fix

Replace Ed25519's dependency on the fragile 5-limb field backend with a
non-`u128` field implementation, or repair the Simple `u128` arithmetic path
first and add a focused OS `Fe25519` field KAT covering:

- `fe_to_bytes(fe_one()) == 01 00...00`
- `fe_mul(2, fe_invert(2)) == 1`
- `ed_point_add(identity, B) == B`
- `ed_scalar_mul(1, B) == B`
- RFC8032 public-key derivation and signature vectors
