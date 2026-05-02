# Bug — `rt_aes{128,256}_encrypt_block_pure expects an array of integers` under interpreter mode

**Filed:** 2026-05-02 (W17-B AES-XTS KAT integration)
**Severity:** High — blocks every pure-Simple AES KAT assertion under interpreter mode (XTS, GCM, CMAC, CCM all affected).

## Symptom

```
runtime: rt_aes128_encrypt_block_pure expects an array of integers
runtime: rt_aes256_encrypt_block_pure expects an array of integers
runtime: rt_aes_decrypt_block_with_expanded expects an array of integers
runtime: rt_tls13_aes128_gcm_encrypt expects an array of integers
runtime: rt_tls13_aes128_gcm_decrypt expects an array of integers
```

Confirmed broken (2026-05-02, latest interpreter):

- `test/unit/lib/crypto/aes128_gcm_nist_vectors_spec.spl`     — 12 / 12 fail
- `test/unit/lib/crypto/aes_cmac_rfc4493_kat_spec.spl`        — multiple fail
- `test/unit/lib/crypto/aes_xts_ieee1619_kat_spec.spl`        — 15 / 15 fail (W17-B, this file)

`test/unit/lib/crypto/sha2_nist_vectors_spec.spl` PASSES (8/8) — it uses
bare-int push (`out.push(0x61)`) and does not wrap through `.to_u8()`.

## Root Cause

`src/compiler_rust/compiler/src/interpreter_extern/simd.rs` lines 47–58:

```rust
fn expect_byte_array(name: &str, value: &Value) -> Result<Vec<u8>, CompileError> {
    match value {
        Value::Array(items) => items
            .iter()
            .map(|item| match item {
                Value::Int(byte) if (0..=255).contains(byte) => Ok(*byte as u8),
                Value::Int(_) => Err(CompileError::runtime(format!("{name} expects byte values in 0..255"))),
                _ => Err(CompileError::runtime(format!("{name} expects an array of integers"))),
            })
            .collect(),
        _ => Err(CompileError::runtime(format!("{name} expects an array argument"))),
    }
}
```

The match arm only accepts `Value::Int`. When pure-Simple code wraps a
`[u8]` arg through `.push(_u8_at(buf, i))` (where `_u8_at` returns `u8`),
the resulting `Value::Array` contains `Value::U8` elements. These are
rejected.

Concrete trigger site — `src/os/crypto/aes128_gcm.spl::aes128_encrypt_block`:

```spl
fn aes128_encrypt_block(plaintext: [u8], round_keys: [u8]) -> [u8]:
    var key: [u8] = rt_array_new_with_cap(16)
    var i: u64 = 0
    while i < 16:
        key.push(_u8_at(round_keys, i))   # _u8_at returns u8 → key is Vec<U8>
        i = i + 1
    rt_aes128_encrypt_block_pure(key, plaintext)   # rejected
```

Same pattern in:
- `src/os/crypto/aes256_gcm.spl::aes256_encrypt_block` (via `aes256_key_expansion`)
- `src/os/crypto/aes_xts.spl::_aes256_expand_key` and helpers

## Workarounds Attempted (all failed)

1. Use `[0x00u8, ...]` literal at call site — `expect_byte_array` rejects.
2. Use `b.push((0x00i64).to_u8())` per
   `interpreter_array_push_u8_literal_lost_2026-05-02.md` workaround —
   value stored correctly but type stays U8, still rejected.
3. Use bare-int push `b.push(0x00)` at call site — but the wrap loop in
   `aes128_encrypt_block` still routes through `.to_u8()`, so the inner
   array hitting `rt_aes128_encrypt_block_pure` is still Vec<U8>.

## Proposed Fix

Two options; option A is preferred:

**A. Loosen `expect_byte_array` to accept `Value::U8` and `Value::I64` too.**

Add match arms:

```rust
Value::U8(byte) => Ok(*byte),
Value::I64(byte) if (0..=255).contains(byte) => Ok(*byte as u8),
```

This makes `[u8]` arrays from any push pattern work, matching the SHA-256
KAT's relaxed expectation and not requiring a sweep of every crypto wrapper.

**B. Remove the wrap loop from `aes128_encrypt_block` and friends.**

Pass `round_keys` directly to `rt_aes128_encrypt_block_pure(round_keys, plaintext)`
without the `_u8_at`/`.push` indirection. The runtime side already extracts
the first 16 bytes (per W13-A wrapper comment in `aes128_encrypt_block`).
This requires touching aes128_gcm.spl + aes256_gcm.spl + every crypto
caller — wider blast radius than option A.

## Related

- `doc/08_tracking/bug/interpreter_array_push_u8_literal_lost_2026-05-02.md`
  — sibling interpreter `[u8]` push regression; this bug is the type-tag
  consequence of the same broken codepath.
- `doc/08_tracking/bug/rt_aes_encrypt_block_into_interpreter_arc_2026-05-02.md`
  — the `_into` Arc-clone bug that W13-A's `_pure` rewrite fixed; the
  current bug is on the `_pure` path itself (different regression).
- `feedback_compile_mode_false_greens.md` — interpreter mode is the trusted
  verification path; this bug undermines it for all AES-bound code.

## Impact on W17-B

`aes_xts_ieee1619_kat_spec.spl` is byte-exact (cross-source verified
against Linux `crypto/testmgr.h` and OpenSSL `evpciph_aes_common.txt`).
All 15 IEEE 1619 / OpenSSL CTS-17 assertions are gated by this bug; they
will fire as-is the moment option A or B lands.
