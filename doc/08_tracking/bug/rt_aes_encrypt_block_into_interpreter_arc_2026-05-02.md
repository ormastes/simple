# rt_aes{128,256}_encrypt_block_into — interpreter-mode Arc-clone discards cipher

**Status:** OPEN. Surfaced 2026-05-02 by W10-C (AES-CMAC) and partially by W10-B (AES-CCM) discipline notes.
**Severity:** silent false-green vector. Affects pure-Simple modules that call `aes128_encrypt_block` / `aes256_encrypt_block` and expect mutated `out` array (CMAC, CCM, possibly GCM fallback path).
**Path:** `bug` track, no compile-mode regression.

## Symptom

In interpreter mode (e.g. `bin/simple test/unit/lib/crypto/aes_cmac_rfc4493_kat_spec.spl`):

- `rt_aes128_encrypt_block_into(key, block, out)` returns `Int(0)` (success)
- But the `out` array (caller's `var out = [0u8; 16]`) is NOT modified
- Caller reads `out` and gets all zeros instead of the cipher

In compile-mode (`bin/simple <script>` self-hosted): works correctly because the compiled extern uses raw FFI pointer mutation via `super::collections::rt_array_set` (see `src/compiler_rust/runtime/src/value/aes.rs:578-605`).

## Root cause

`src/compiler_rust/compiler/src/interpreter_extern/simd.rs:209-227` (AES-128) and `:249-266` (AES-256):

```rust
pub fn rt_aes128_encrypt_block_into(args: &[Value]) -> Result<Value, CompileError> {
    let key = expect_byte_array("rt_aes128_encrypt_block_into", &args[0])?;
    let block = expect_byte_array("rt_aes128_encrypt_block_into", &args[1])?;
    let _out = expect_byte_array("rt_aes128_encrypt_block_into", &args[2])?;  // ← validated, then discarded
    if key.len() != 16 || block.len() != 16 {
        return Ok(Value::Int(1));
    }
    if aes128_encrypt_one_block(&key, &block).is_some() {
        Ok(Value::Int(0))   // ← cipher computed but THROWN AWAY
    } else {
        Ok(Value::Int(1))
    }
}
```

The contract divergence between modes is documented at `simd.rs:203-208`:

> NOTE: in interpreter mode the runtime `Value::Array` is `Arc<Vec<Value>>`; the args we receive are clones of the caller's Arc, so mutation of `out` does NOT propagate back to the caller. This matches the AES-128-GCM caller's design (it's an unused fallback path when rt_tls13_aes128_gcm_encrypt returns non-empty). Compile-mode (raw FFI pointer) does mutate the caller's array in place via rt_array_set.

The "unused fallback path" claim is **no longer accurate** — W10-B (AES-128-CCM) and W10-C (AES-CMAC) actively use `aes128_encrypt_block` from `src/os/crypto/aes128_gcm.spl`, which routes through this extern and reads `out` after.

## Affected callers (suspected)

- **W10-C aes_cmac.spl** — explicitly noted in W10-C closeout report: byte-equality assertions DEFERRED for this reason.
- **W10-B aes128_ccm.spl** — claimed 12/12 PASS with RFC 3610 §8 byte-exact, but if interpreter-mode false-green from `rt_aes128_encrypt_block_into` is involved, those PASSes may be load-only ghosts. **Needs audit after W11-A test_runner false-green fix lands.**
- **W8-3 aes256_gcm.spl `gctr256`** — depends on whether `_aes256_encrypt_block_with_schedule` routes through the broken extern or stays SIMD-only via `rt_simd_aes_round_u8x16`. W8-3 reported 6/6 PASS via `rt_aes256_encrypt_block_into` — same audit risk.
- Any future caller that pre-fills `out` and expects in-place cipher.

## Fix options

### Option A — add new extern returning cipher (recommended)

Add `rt_aes128_encrypt_block_pure(key, block) -> [u8]` and `rt_aes256_encrypt_block_pure(key, block) -> [u8]` mirroring the pattern of `rt_tls13_aes128_gcm_encrypt` at `simd.rs:231-244`:

```rust
pub fn rt_aes128_encrypt_block_pure(args: &[Value]) -> Result<Value, CompileError> {
    let key = expect_byte_array("rt_aes128_encrypt_block_pure", &args[0])?;
    let block = expect_byte_array("rt_aes128_encrypt_block_pure", &args[1])?;
    if key.len() != 16 || block.len() != 16 {
        return Ok(Value::array(vec![]));
    }
    let cipher = aes128_encrypt_one_block(&key, &block).unwrap_or([0u8; 16]);
    Ok(Value::array(cipher.iter().map(|b| Value::Int(*b as i64)).collect()))
}
```

Update Simple-side `aes128_encrypt_block` in `src/os/crypto/aes128_gcm.spl` to use the new extern:

```spl
fn aes128_encrypt_block(key: [u8], block: [u8]) -> [u8] {
    return rt_aes128_encrypt_block_pure(key, block)
}
```

Same for AES-256. **Required:**
- New runtime functions in `src/compiler_rust/runtime/src/value/aes.rs` (compile-mode `extern "C"` form returning a `RuntimeValue` array).
- Re-export in `src/compiler_rust/runtime/src/value/mod.rs`.
- Interpreter-mode handlers in `src/compiler_rust/compiler/src/interpreter_extern/simd.rs`.
- Dispatch entry in `src/compiler_rust/compiler/src/interpreter_extern/mod.rs`.
- Caller updates in `src/os/crypto/aes128_gcm.spl` and `src/os/crypto/aes256_gcm.spl`.
- `bash scripts/bootstrap/bootstrap-from-scratch.sh --deploy` per `feedback_extern_bootstrap_rebuild.md`.

Estimated effort: **1 wave / 1 agent / ~30-45 min** including bootstrap rebuild.

### Option B — keep `_into` but mutate caller via shared interior-mutability

Wrap `Vec<Value>` inside `Value::Array` with `Arc<RwLock<Vec<Value>>>` or `Arc<Mutex<Vec<Value>>>`. Then `Arc::clone` shares the same lock, and mutation propagates. **Rejected** — touches the entire Value model, ripples through every Array consumer, blast radius too high for one wave.

### Option C — make interpreter-mode handler use sticky-write contract

Detect when `args[2]` is a uniquely-addressable runtime slot and write back via the runtime's existing `rt_array_set` accessor. **Unclear whether the interpreter-mode runtime exposes the address chain back to the caller's local; needs investigation. Defer to compiler-side specialist.**

## Preferred path

Option A. Localized to runtime + 2-3 caller files + bootstrap rebuild. Doesn't touch compile-mode behavior (existing `_into` extern stays as-is for compile-mode and any in-place callers).

## Verification after fix

1. Inject `to_equal(0xc36cc1f5...)` into one CMAC RFC 4493 §4.1 byte assertion in `test/unit/lib/crypto/aes_cmac_rfc4493_kat_spec.spl` (currently spec-only structural).
2. Run `bin/simple test test/unit/lib/crypto/aes_cmac_rfc4493_kat_spec.spl` — must FAIL (proving assertion runs and bytes don't match before fix).
3. Apply Option A.
4. Rebootstrap.
5. Re-run — must PASS byte-exact.
6. Audit W10-B aes128_ccm spec for the same load-only false-green class.

## Cross-references

- `feedback_extern_bootstrap_rebuild.md` — bootstrap procedure.
- `feedback_compile_mode_false_greens.md` — broader false-green pattern.
- W11-A `8b8f64c32453 fix(test_runner): execute infix expect assertions in interpreter mode` — orthogonal fix for ANOTHER false-green class; this AES bug is independent.
- W10-C closeout report (Wave 10 task #65) — original surface.
- `src/compiler_rust/runtime/src/value/aes.rs:578-605` — compile-mode (working) implementation.
- `src/compiler_rust/compiler/src/interpreter_extern/simd.rs:209-227, 249-266` — interpreter-mode (broken) handlers.
