# Rust seed checked-sign result constructs `Vec` where `Value::Array` owns `Arc<Vec>`

Date: 2026-08-22
Status: PARTIAL — authority and Phase 2 pass; focused Rust test pending
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
