# Bug: aes128_gcm_decrypt — `type mismatch: cannot convert string to int` (refined: interpreter Arc-clone out-param drop)

**Date:** 2026-05-01
**Status: FIXED 2026-05-01 (refined fix). Two distinct root causes, fixed in two waves:**

**Wave 1 (T3, commit `654e9b3911`)** — semantic-check error from leftover
`_debug_bytes4` / `_debug_bytes16` / `_debug_bytes_all` log-scaffolding helpers
in `aes128_gcm_decrypt` tripped the semantic checker on f-string-interpolated
`u8`/`u64` values. Fix: deleted the call sites + helpers + `klog_api` import.
That cleared the semantic error but did NOT make decrypt pass — the symptom
shifted from semantic error to runtime "expected false to equal true" because
the spec then reached the `Aes128GcmResult.Err` arm.

**Wave 2 (T21 / 2026-05-01, refined root cause)** — pure-Simple decrypt failed
under `bin/simple` (interpreter mode) because `aes128_encrypt_block` calls
`rt_aes128_encrypt_block_into(key, block, out)` expecting the runtime to
mutate the `out` array. The interpreter path
(`compiler_rust/compiler/src/interpreter_extern/simd.rs::rt_aes128_encrypt_block_into`)
clones `Value::Array(Arc<Vec<Value>>)` arguments by value via
`expect_byte_array`; mutation never propagates back to the caller, so
`output` stays all-zeros and the computed `expected_tag` never matches. The
encrypt path was masked because `aes128_gcm_encrypt` short-circuits to the
`rt_tls13_aes128_gcm_encrypt` extern (which RETURNS a fresh `[u8]` and never
exercises the broken out-param mutation). T21's "Arc-clone mutation
propagation" framing was directionally correct; the concrete storage is a
stable header + heap data buffer (not literally `Arc<Vec<Value>>`), but the
interpreter's `Value` clone discipline produces the same observable behaviour.

**Fix:** Add `rt_tls13_aes128_gcm_decrypt` and `rt_tls13_aes256_gcm_decrypt`
extern fast-paths that mirror the encrypt fast-path (return-style `[u8]` with
status-prefix encoding: `[]` = invalid input, `[0x00]` = tag mismatch,
`[0x01,...]` = success+plaintext). Both `aes128_gcm_decrypt` and
`aes256_gcm_decrypt` call the fast-path before falling through to the
pure-Simple chain. The pure-Simple path is preserved verbatim for baremetal
fallback (when the runtime returns `[]`).

**Component:** `src/os/crypto/aes128_gcm.spl`, `src/os/crypto/aes256_gcm.spl`,
`src/compiler_rust/runtime/src/value/aes.rs`,
`src/compiler_rust/compiler/src/interpreter_extern/simd.rs`,
`src/compiler_rust/compiler/src/interpreter_extern/mod.rs`,
`src/compiler_rust/runtime/src/value/mod.rs`.

**Discovered-by:** AES-128-GCM and AES-256-GCM NIST SP 800-38D Appendix B
specs against `src/compiler_rust/target/bootstrap/simple`.

**Resolution:** All 12 AES-128-GCM it-blocks (TC1–TC4 encrypt, decrypt, and
tag-corruption rejection) PASS, all 12 AES-256-GCM it-blocks (TC13–TC16) PASS
post-bootstrap-rebuild. Constant-time tag compare preserved (runtime side
uses byte-OR accumulation). Bootstrap stage 3 SHA verified.

**Latent issue surfaced (separate, NOT fixed here):** The interpreter's
`expect_byte_array` returning a `Vec<u8>` clone means *any* extern with an
`out: [u8]` mutation contract is broken in interpreter mode. The
`rt_aes128_encrypt_block_into` and `rt_aes256_encrypt_block_into` call sites
in `aes128_gcm.spl` / `aes256_gcm.spl` are now technically dead via the
fast-path short-circuit, but the externs themselves remain and the bug
they document in their source comments (`simd.rs:193-200`) is still live.
TODO: file a follow-up bug doc for that latent class of FFI issues, or
delete the broken externs once no caller uses them.

## Summary

After registering the four `rt_aes_*` / `rt_tls13_aes128_gcm_encrypt` externs
(see `aes128_gcm_stub_2026-05-01.md`, FIXED), `aes128_gcm_encrypt` runs cleanly
and matches NIST SP 800-38D Appendix B vectors TC1–TC4 byte-for-byte. The
companion `aes128_gcm_decrypt` path fails with a semantic error before any
runtime code runs:

```
semantic: type mismatch: cannot convert string to int
```

## Repro

```bash
src/compiler_rust/target/bootstrap/simple test \
    test/unit/lib/crypto/aes128_gcm_nist_vectors_spec.spl
```

8 of 12 it-blocks fail (the 4 encrypt blocks pass):

- TC1 decrypt: correct tag succeeds with empty plaintext
- TC1 decrypt: corrupted tag is rejected
- TC2 decrypt: correct tag returns original plaintext
- TC2 decrypt: corrupted tag is rejected
- TC3 decrypt: correct tag returns original plaintext
- TC3 decrypt: corrupted tag is rejected
- TC4 decrypt: correct tag returns original plaintext
- TC4 decrypt: corrupted tag is rejected

All 8 fail at the semantic stage with the same `cannot convert string to int`
message — no line/column reported by the test harness output.

## Suspected Location

`fn aes128_gcm_decrypt(key, nonce, ciphertext, aad, tag) -> Aes128GcmResult`
(declared near line 559 of `src/os/crypto/aes128_gcm.spl`). The encrypt path
(which uses the same helpers `gctr`, `ghash`, `aes128_key_expansion`,
`_make_j0`) compiles and runs cleanly, so the failure is specific to the
decrypt-only constructs (likely a literal in the Aes128GcmResult.Err arm
or the constant-time tag-compare).

## Out-of-Scope-For

`aes128_gcm_stub_2026-05-01.md` (extern registration). That bug is FIXED
independently — encrypt vectors prove the registration is correct.

## Next Steps

1. Locate the failing line via a smaller standalone repro (e.g., a 5-line
   test that just calls `aes128_gcm_decrypt` with empty inputs).
2. Inspect the decrypt body for any string-typed expression that flows into
   an integer context (likely in an `Err(...)` arm or in the tag-compare
   loop).
3. Fix or refactor; re-run the spec to drive 12/12 PASS.
