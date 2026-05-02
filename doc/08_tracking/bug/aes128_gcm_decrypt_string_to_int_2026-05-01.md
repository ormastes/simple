# Bug: aes128_gcm_decrypt — `type mismatch: cannot convert string to int`

**Date:** 2026-05-01
**Status: FIXED 2026-05-01 — root cause: leftover `_debug_bytes4` / `_debug_bytes16` / `_debug_bytes_all` log-scaffolding helpers in `aes128_gcm_decrypt` tripped the semantic checker on f-string-interpolated `u8`/`u64` values; encrypt was unaffected because its fast-path `rt_tls13_aes128_gcm_encrypt` extern returns before any debug call runs. Fix: deleted the call sites in decrypt and removed the unused helpers + `klog_api` import. AES-GCM core (key expansion, GHASH, GCTR, tag compare) was correct all along.**
**Component:** `src/os/crypto/aes128_gcm.spl` (decrypt path)
**Discovered-by:** AES-128-GCM NIST SP 800-38D Appendix B spec post-extern-fix
**Resolution:** All 12 it-blocks (4 encrypt + 4 decrypt round-trip + 4 tag-corruption negative cases) PASS in interpreter mode against `src/compiler_rust/target/bootstrap/simple` — see `test/unit/lib/crypto/aes128_gcm_nist_vectors_spec.spl`. Constant-time tag compare preserved; no extern added.

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
