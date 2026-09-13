# Bug: asym_typed_keypair — tuple-element corruption risk on cross-module return

## Closed 2026-09-13 — Does not reproduce: cross-module tuple elements survive intact

- **measured** (Rust seed `bin/simple` v1.0.0-rc.1, Windows): module A returns `([u8], [u8])` as `([1u8, 2u8], [3u8, 4u8])`; module B accesses `k.0[0] k.0[1] k.1[0] k.1[1]` and prints `1 2 3 4`. No corruption at the cross-module tuple-element accessor.
- **inferred**: the entry was filed as a "corruption risk" with a workaround already applied and no live crash, referencing `feedback_tuple4_element_corruption.md`. With the accessor now correct, the `Ed25519KeyPair` wrapper in `asym.spl` is optional simplification, not a defect.
- Deliberately NOT done here: removing that wrapper. It is a public signature change in `src/lib`, outside this triage's remit, and the entry itself frames it as a follow-up.

**ID:** asym_typed_keypair_tuple_corruption_2026-06-15
**Date:** 2026-06-15
**Status:** CLOSED 2026-09-13 (does not reproduce). **Severity:** Workaround applied — no current crash

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
