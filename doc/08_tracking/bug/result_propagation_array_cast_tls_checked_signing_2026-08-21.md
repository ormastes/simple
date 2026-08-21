# Result propagation mis-lowers checked TLS signature arrays

**Date:** 2026-08-21
**Status:** Compiler cast fixed; deployed bootstrap verification pending

## Reproduction

In `build_certificate_verify_checked`, assigning a checked foreign result with
the compact form below passes a direct file check but fails when the enclosing
TLS unit spec is executed:

```simple
sig = ed25519_sign_pkcs8_checked(key, message)?
```

Observed diagnostic:

```text
semantic: type mismatch: unsupported cast target type:
Array { element: Simple("u8"), size: None }
```

The compact propagation reaches the common runtime type assertion for `[u8]`.
That assertion previously rejected the packed `ByteArray` representation even
though it already is the canonical dynamic byte-array value. The interpreter
now treats packed `[u8]` and ordinary dynamic-array assertions as identity
casts. This is zero-copy and does not add allocation or traversal to the TLS
signing path. The explicit `match Ok(signature) / Err(error)` remains because
it preserves the foreign diagnostic at the handshake boundary.

## Verification status

The focused Rust unit `packed_u8_array_type_assertion_is_zero_copy` passes.
The TLS unit spec still reports the old cast error because `bin/simple` is a
previously deployed bootstrap executable and does not contain the current Rust
compiler source change. Its three-run session cap has been reached, so it was
not rerun again. After deploying a fresh compiler, a future session must run
`test/01_unit/os/tls13/server_accept_spec.spl` once.
