# Rust seed checked-sign result constructs `Vec` where `Value::Array` owns `Arc<Vec>`

Date: 2026-08-22
Status: FIXED (closed 2026-11-02; see Closure)
Owner: Rust seed interpreter checked-sign SFFI bridge
Severity: P0 for current ARM64 bootstrap / SimpleOS QEMU continuation

## Exact failure

A fresh current-main trust-root bootstrap fails before Phase 2 with Rust E0308
at both branches of `checked_sign_value` in
`compiler/src/interpreter_extern/signatures.rs`. `Value::Array` requires
`Arc<Vec<Value>>`, while the helper passed `Vec<Value>` directly.

This is below the pure-Simple boundary: the checked signature declarations and
dispatch reach the seed bridge correctly, but the Rust authority cannot compile.
The fix converts each vector through `Into<Arc<Vec<Value>>>`; it does not alter
the status/payload pair contract or introduce a fallback.

## Evidence required

1. Bootstrap-profile `cargo check` passes for `simple-compiler`.
2. `checked_signing_distinguishes_success_from_bridge_failure` passes, covering
   a successful Ed25519 pair and malformed RSA/Ed25519/ECDSA pairs.
3. The canonical strict trust-root Phase 2 admits before this record resolves.

## Current evidence

The rebuilt Rust authority passed and the canonical strict Phase 2 admitted at
SHA-256 `acd84663e494a8046bc8745b3bd380f03b22dacc15ef710c905beeb4d3fb53fd`.
The preserved bootstrap Cargo target is immutable, so a direct focused test was
not run against it; criterion 2 remains open and this record is not resolved.

Revalidated 2026-11-02: still plausible because doc Status is PARTIAL with the focused Rust test still pending.

## Closure (2026-11-02, opus-opf-7)

Status: FIXED. Checked against current policy/design: still valid as a
Rust-seed type-shape bug. The erased-generics, nil-in-unsafe, Any-in-unsafe,
SDN, per-file pipeline and HIR/MIR target policies do not touch it. It is
already fixed in source:
`src/compiler_rust/compiler/src/interpreter_extern/signatures.rs:153`
`checked_sign_value` now builds both branches with `Value::array(vec![...])`,
which wraps the vector in `Arc`. The fix landed in d46287b6352 and 9a674f7b45b.

Criterion 2 is now met. On Windows, with clang-cl and its own target dir, on
origin/release/1.0.0 5722fb002df:
`cargo test -p simple-compiler --lib checked_signing_distinguishes` gives
`test interpreter::interpreter_extern::signatures::tests::checked_signing_distinguishes_success_from_bridge_failure ... ok`
and `test result: ok. 1 passed`.

This is not related to the stage2_next worker AV after load_sources. That bug
was a compile-time E0308, and a seed with it cannot build at all.
