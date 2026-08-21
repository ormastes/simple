# Result propagation mis-lowers checked TLS signature arrays

**Date:** 2026-08-21
**Status:** Open compiler bug; explicit-match workaround applied

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

The explicit `match Ok(signature) / Err(error)` form checks successfully and
preserves the intended typed-error contract. The compiler should lower both
forms equivalently for `Result<[u8], text>`.

## Verification status

The TLS unit spec was run three times while isolating the diagnostic, reaching
the session verify/fix cap. It was not rerun after applying the explicit-match
workaround. The changed builder passes `bin/simple check`, and the checked-call
source audit passes. A future fresh session must rerun
`test/01_unit/os/tls13/server_accept_spec.spl` once.
