# Interpreter: signature_ffi.ed25519_sign shadows os.crypto.ed25519.ed25519_sign (arity conflict)

Status: FIXED 2026-05-19 — renamed `signature_sffi.ed25519_sign` → `ed25519_sign_pkcs8`; updated all callers

**Filed:** 2026-05-03  
**Discovered during:** COSE RFC 9052 KAT spec fix (cose_rfc9052_kat_spec.spl)
**Status:** FIXED 2026-05-19 — renamed `signature_sffi.ed25519_sign` → `ed25519_sign_pkcs8`; updated all callers.

Note: the 2026-05-10 "FIXED" entry was incorrect — the root-cause rename had not been applied.
That commit predated the `ffi → sffi` rename refactor; the shadow persisted in `signature_sffi.spl`.

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

`src/lib/nogc_sync_mut/io/signature_sffi.spl` (formerly `signature_ffi.spl`) defines:

```spl
fn ed25519_sign(pkcs8: [u8], message: [u8]) -> [u8]:
```

This is a 2-arg variant (pkcs8 + message, no separate public key). When
`os.crypto.ecdsa_p256` is imported, it transitively loads `signature_sffi` via:

```
os.crypto.ecdsa_p256 → use std.nogc_sync_mut.io.signature_sffi
```

The interpreter's function table then has two `ed25519_sign` entries with different
arities. The 2-arg `signature_ffi` version wins the lookup (last-write or first-wins
collision), causing all calls to the 3-arg `os.crypto.ed25519.ed25519_sign` to fail
at semantic analysis with an arity mismatch.

## Affected paths

- Any module importing both `os.crypto.ed25519` and `os.crypto.ecdsa_p256` (directly or
  transitively).
- `src/os/crypto/cose.spl` imports both at the top level, so all Sign1 tests in
  `test/01_unit/os/crypto/cose_rfc9052_kat_spec.spl` fail.

## Workaround

Remove `os.crypto.ecdsa_p256` from the import chain when testing EdDSA Sign1 paths.
The COSE KAT spec drops the Sign1 describe block until this is resolved (see commit
`fix(crypto): COSE spec — drop Sign1 blocked by signature_ffi shadow, expand Mac0 KAT`).

## Fix applied (2026-05-19)

Option 1 was chosen: rename the 2-arg wrapper in `signature_sffi.spl` to
`ed25519_sign_pkcs8`, making the naming consistent with its PKCS#8-key calling
convention and eliminating the name collision.

Changed files:
- `src/lib/nogc_sync_mut/io/signature_sffi.spl` — renamed `fn ed25519_sign` → `fn ed25519_sign_pkcs8`
- `src/lib/nogc_async_mut/io/signature_sffi.spl` — updated re-export list
- `src/os/tls13/server.spl` — updated import + 2 call sites
- `src/os/tls13/tls13_part3.spl` — updated 1 call site

The Rust interpreter dispatch (`signatures.rs`, `mod.rs`) was not changed — it
uses `rt_ed25519_sign` which was never part of the shadow.

## Discarded fix options

2. Qualify all `ed25519_sign` call sites by module path — would require changes
   at every call site across multiple modules without fixing the underlying naming.
3. Detect and error on duplicate names during import loading — a useful hardening
   but does not fix the existing caller breakage.

## Re-verification (2026-05-27)

`test/01_unit/os/crypto/cose_rfc9052_kat_spec.spl` now passes 8/8 in interpreter
mode. The remaining failure after the original shadow rename was not another
Ed25519 collision; `cose.spl` depended on SMF-only `std.common.cbor.*` helpers
that were unavailable to the interpreter. COSE now carries the small CBOR subset
it needs locally, and the Mac0 KAT length guard was corrected from 63 to 62
bytes because a 20-byte CBOR byte string has a one-byte header.
