# Bug: `quic_aead_encrypt` failed in interpreter / SEGFAULTed under JIT — RESOLVED

- **ID:** quic_aead_encrypt_fails_interp_segfaults_jit_2026-06-16
- **Severity:** P1 (RED spec + native crash)
- **Status:** RESOLVED 2026-06-16 (pure-Simple fix; underlying compiler bug filed separately)
- **Area:** std.common.crypto.aes_gcm / cross-module private-symbol resolution

## Symptom
`test/01_unit/lib/nogc_async_mut/quic/quic_aead_spec.spl` was RED — 2/3 `it` passed;
the encrypt KAT (`expect(_enc()).to_equal("d6b38a78…365f87")`) failed. Under
`bin/simple run` (JIT) the same call **segfaulted** (rc=139). Decrypt round-trip and
tamper-reject passed.

## Root cause — cross-module private-helper name collision
The spec fixture is CORRECT (independently confirmed vs Python `cryptography`:
`d6b38a7873b8d79ee6855b9ddc6d15e663365f87`). The bug was in symbol resolution.

Decisive asymmetry: encrypt and decrypt route through the same `aes_gcm` helpers
EXCEPT encrypt's tail call `_append_bytes(ciphertext, tag)` — the only symbol unique
to the failing path.

`aes_gcm.spl:440` defined `fn _append_bytes(a:[u8], b:[u8]) -> [u8]` (returns the
concatenation). But `quic_crypto.spl` imports `hkdf` (line 21), and `hkdf.spl:59`
defines a *different* `fn _append_bytes(dst:[i64], src:[i64])` with **no return**
(void/mutate). The module loader collapses same-named **private** (`_`-prefixed)
functions across the import graph into one symbol, so `aes128_gcm_encrypt`'s call to
`_append_bytes` resolved to hkdf's **void** version → returned nil → `_bytes_to_hex_u8(nil)`
→ `nil.len()` (interpreter) / NULL deref SIGSEGV (JIT). Decrypt never calls
`_append_bytes`, so it was unaffected. (23 incompatible `_append_bytes` defs exist
repo-wide — see the compiler bug.)

## Minimal repro (pre-fix)
```
# Merely importing quic_crypto poisons a DIRECT aes128_gcm_encrypt call:
use std.io.quic.quic_crypto.{quic_compute_nonce}
use std.common.crypto.aes_gcm.{aes128_gcm_encrypt}
fn main():
    val ct = aes128_gcm_encrypt(mk(16), mk(12), mk(4), mk(22))   # SIGSEGV under JIT
```

## Fix
Renamed the private helper to a module-unique name to dodge the collision
(`aes_gcm.spl`: `_append_bytes` → `_aesgcm_append_bytes`, def + 2 call sites for
aes128 + aes256). Pure-`.spl`, no seed rebuild.

## Verification
- `quic_aead_spec` → **3/0** (was 2/3).
- `quic_aead_encrypt` under JIT → no crash, output == RFC 9001 KAT exactly.
- `aes128_gcm_nist_vectors_spec` → **12/0** (no regression).

## Residual
The real defect is in the compiler (private symbols are not namespaced per module).
Filed as `compiler_cross_module_private_symbol_collision_2026-06-16`. Until that is
fixed, any module whose import graph pulls in two `_`-prefixed helpers of the same
name with different signatures/return-arity is a latent crash — the rename here only
inoculates aes_gcm.
