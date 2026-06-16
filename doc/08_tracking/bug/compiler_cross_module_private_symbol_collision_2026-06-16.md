# Bug: private (`_`-prefixed) functions collide across modules — wrong fn called

- **ID:** compiler_cross_module_private_symbol_collision_2026-06-16
- **Severity:** P1 (silent wrong-result + SIGSEGV; broad latent surface)
- **Status:** OPEN
- **Area:** compiler — module loader / symbol resolution (interpreter + JIT)

## Summary
Private helper functions (conventionally `_`-prefixed, file-local by intent) are
**not namespaced per module**. When two modules in the same import graph each define
a function with the same name but different signatures / return arity, the loader
collapses them to one symbol. Calls then dispatch to the WRONG definition — returning
nil/garbage in the interpreter and NULL-dereferencing (SIGSEGV) under the Cranelift
JIT.

This is a correctness-and-safety bug, not just hygiene: a callee can silently lose
its return value.

## Concrete instance (how it was found)
- `aes_gcm.spl:440` `fn _append_bytes(a:[u8], b:[u8]) -> [u8]` (returns concat).
- `hkdf.spl:59`    `fn _append_bytes(dst:[i64], src:[i64])` (void / in-place).
- `quic_crypto.spl` imports both aes_gcm and hkdf. `aes128_gcm_encrypt`'s
  `_append_bytes(ct, tag)` dispatched to hkdf's **void** version → returned nil →
  `nil.len()` (interp) / SIGSEGV (JIT). Decrypt (no `_append_bytes`) was fine.
  See `quic_aead_encrypt_fails_interp_segfaults_jit_2026-06-16` (worked around by
  renaming aes_gcm's helper).

## Scope of the landmine
`grep -rn "fn _append_bytes" src/` → **23** definitions with at least 3 distinct
signatures (`-> [u8]`, void-mutate `[u8]`, void-mutate `[i64]`) across crypto, hkdf,
http/h2/ws writers, quic_packet, tls13, ssh, gzip/lz4, stun/socks5, nvfs. Any module
graph that unifies two of these mis-dispatches. `_append_bytes` is just the helper
that happened to collide here; the same applies to every duplicated `_`-prefixed
name (`_u8_at`, `_make_j0`, etc.).

## Repro (minimal)
```
use std.io.quic.quic_crypto.{quic_compute_nonce}   # pulls in hkdf._append_bytes (void)
use std.common.crypto.aes_gcm.{aes128_gcm_encrypt} # uses aes_gcm._append_bytes (-> [u8])
fn main():
    # before the aes_gcm rename: SIGSEGV under `bin/simple run`, nil.len() under interp
    aes128_gcm_encrypt(mk(16), mk(12), mk(4), mk(22))
```

## Fix options
1. **Proper fix:** mangle private (`_`-prefixed, non-exported) function symbols with a
   per-module prefix in the loader/codegen, so two modules' `_append_bytes` are
   distinct symbols. Both interpreter symbol table and Cranelift function ids.
2. **Detection stopgap:** a lint that flags two in-scope private functions of the same
   name with differing signature/return arity (would have caught this).
3. **Interim hygiene:** the per-instance rename used for aes_gcm — does NOT address the
   systemic bug; other graphs remain exposed.

## Notes
Related prior cross-module JIT work: `rt_extern_registration_and_jit_cross_module_gap`
(imported class methods → NULL-GOT SIGSEGV). This is the *private-function* analogue
and is value-corrupting even in the interpreter, so it is not caught by the existing
JIT first-unresolved-import guard.
