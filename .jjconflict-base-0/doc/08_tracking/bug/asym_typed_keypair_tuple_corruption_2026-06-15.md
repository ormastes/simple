# Bug: asym_typed_keypair — tuple-element corruption risk on cross-module return

**ID:** asym_typed_keypair_tuple_corruption_2026-06-15
**Date:** 2026-06-15
**Severity:** Workaround applied — no current crash

## Summary

`ed25519_keypair_from_seed` returns `([u8], [u8])`.  When a function in one
module returns a tuple whose elements are then accessed via `.0`/`.1` in
another module, the interpreter can corrupt the accessed values (known issue:
`feedback_tuple4_element_corruption.md`).

## Workaround

`asym.spl` wraps the result in a `struct Ed25519KeyPair { secret: SecretKey,
public: PublicKey }` before returning it across the module boundary.  The
underlying `kp.0` / `kp.1` access happens inside `ed25519_typed_keypair` —
same module as the core call — so the corruption window is closed.

## Fix

Fix the interpreter tuple-element accessor to correctly handle cross-module
tuple return; then `Ed25519KeyPair` can be removed and the function signature
simplified to return `(SecretKey, PublicKey)` directly.
