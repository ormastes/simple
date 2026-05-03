# Interpreter: signature_ffi.ed25519_sign shadows os.crypto.ed25519.ed25519_sign (arity conflict)

**Filed:** 2026-05-03  
**Discovered during:** COSE RFC 9052 KAT spec fix (cose_rfc9052_kat_spec.spl)

## Symptom

When a test file imports both `os.crypto.ed25519.{ed25519_sign}` (3-arg: seed, pub_key, message)
and any module that transitively imports `std.nogc_sync_mut.io.signature_ffi` (e.g.
`os.crypto.ecdsa_p256`), calling `ed25519_sign(seed, pub_key, message)` with 3 arguments
produces:

```
semantic: function expects 2 argument(s), but more were provided
```

## Minimal repro

```spl
use os.crypto.ed25519.{ed25519_keypair_from_seed, ed25519_sign}
use os.crypto.ecdsa_p256.{ecdsa_p256_sign_fixed, ecdsa_p256_verify_fixed}
# ... fn that calls ed25519_sign(seed, pub_key, msg)  -> semantic error
```

Without the `ecdsa_p256` import, `ed25519_sign(seed, pub_key, msg)` works correctly.

File: `/tmp/ecdsa_combo_test.spl` (repro built 2026-05-03)

## Root cause

`src/lib/nogc_sync_mut/io/signature_ffi.spl` line 132 defines:

```spl
fn ed25519_sign(pkcs8: [u8], message: [u8]) -> [u8]:
```

This is a 2-arg variant (pkcs8 + message, no separate public key). When
`os.crypto.ecdsa_p256` is imported, it transitively loads `signature_ffi` via:

```
os.crypto.ecdsa_p256 → use std.nogc_sync_mut.io.signature_ffi
```

The interpreter's function table then has two `ed25519_sign` entries with different
arities. The 2-arg `signature_ffi` version wins the lookup (last-write or first-wins
collision), causing all calls to the 3-arg `os.crypto.ed25519.ed25519_sign` to fail
at semantic analysis with an arity mismatch.

## Affected paths

- Any module importing both `os.crypto.ed25519` and `os.crypto.ecdsa_p256` (directly or
  transitively).
- `src/os/crypto/cose.spl` imports both at the top level, so all Sign1 tests in
  `test/unit/os/crypto/cose_rfc9052_kat_spec.spl` fail.

## Workaround

Remove `os.crypto.ecdsa_p256` from the import chain when testing EdDSA Sign1 paths.
The COSE KAT spec drops the Sign1 describe block until this is resolved (see commit
`fix(crypto): COSE spec — drop Sign1 blocked by signature_ffi shadow, expand Mac0 KAT`).

## Fix options

1. Rename `signature_ffi.ed25519_sign` → `_rt_ed25519_sign_pkcs8` (private, matches
   its pkcs8-key calling convention) and update its callers. Requires bootstrap rebuild.
2. Qualify all `ed25519_sign` call sites in the interpreter by module path when both
   are in scope.
3. Detect and error on duplicate function names with different arities during import
   loading (reject shadowing rather than silently picking one).
