# Bug: interpreter-mode externs with `out: [u8]` parameters silently drop mutations

**Date:** 2026-05-01
**Status:** OPEN — workaround in place for AES-GCM (decrypt fast-path), latent for other extern call sites.
**Component:** `src/compiler_rust/compiler/src/interpreter_extern/` — specifically the `expect_byte_array` helper at `simd.rs:40-52`.

## Summary

When an `extern fn foo(... out: [u8])` is invoked in **interpreter mode**
(`bin/simple <script.spl>`), the interpreter dispatches via
`compiler/src/interpreter_extern/<module>.rs` which uses
`expect_byte_array(name, value)` to convert each `Value::Array` argument into
a fresh `Vec<u8>` by *cloning* every element (`simd.rs:40-52`). The Rust
implementation then writes its result into the cloned `Vec<u8>`, but that Vec
is a **local copy** — the original `Value::Array(Arc<Vec<Value>>)` held by
the .spl caller is never mutated. The .spl side observes `out` unchanged
(zeros if it pre-filled, undefined otherwise) and silently produces wrong
results.

This works correctly in **compile mode** because the C-ABI extern receives
the runtime `RuntimeValue` pointer and writes through `super::collections::rt_array_set`,
which mutates the shared `RuntimeArray` data buffer in place. The two paths
diverge.

## Discovered

`aes128_gcm_decrypt` / `aes256_gcm_decrypt` failed every NIST SP 800-38D
correct-tag test in interpreter mode:

```
TC1 decrypt: correct tag succeeds with empty plaintext — expected false to equal true
```

Root cause traced via a minimal repro that called `aes128_encrypt_block`
(which delegates to `rt_aes128_encrypt_block_into`) on the FIPS 197 zero-key
zero-block vector:

```
rt_aes128_encrypt_block_into rc=0
output (after extern call) = 00000000000000000000000000000000   <-- wrong, all zeros
expected                   = 66e94bd4ef8a2c3b884cfa59ca342b2e
```

The extern returned success (rc=0) but `output` was never written. Compiler
source already documents the bug — `simd.rs:193-200` says:

> in interpreter mode the runtime `Value::Array` is `Arc<Vec<Value>>`; the
> args we receive are clones of the caller's Arc, so mutation of `out` does
> NOT propagate back to the caller. This matches the AES-128-GCM caller's
> design (it's an unused fallback path when rt_tls13_aes128_gcm_encrypt
> returns non-empty).

The "unused fallback" claim is wrong: `aes128_gcm_decrypt` calls
`aes128_encrypt_block` (and thus `rt_aes128_encrypt_block_into`) on the
primary path, with no encrypt fast-path to short-circuit it.

## Affected externs (audit)

Any extern with an `out: [u8]` (or any `[u8]` mutated as side-effect) is
broken in interpreter mode. Known instances:

- `rt_aes128_encrypt_block_into(key, block, out: [u8]) -> i64` (worked around)
- `rt_aes256_encrypt_block_into(key, block, out: [u8]) -> i64` (worked around)

Any future `*_into` extern would inherit the same bug. **TODO:** audit other
extern declarations in `src/compiler_rust/compiler/src/interpreter_extern/*.rs`
for `_out` discards (search pattern: `let _out = expect_byte_array`).

## Workaround

For AES-GCM, the workaround was to add return-style fast-path externs
(`rt_tls13_aes*_gcm_decrypt`) that return a fresh `[u8]` instead of mutating
an out-param, mirroring the encrypt pattern. Status-prefixed encoding lets
a single `[u8]` carry "OK + plaintext" or "tag mismatch" outcomes:
- `[]` = invalid input → caller falls back to pure-Simple
- `[0x00]` = tag mismatch
- `[0x01, ...]` = success; trailing bytes are the result

Landed in commit `6bbbc80a` (fix(aes-gcm): decrypt fast-path extern...).

## Permanent fix candidates

1. **Have `expect_byte_array` accept the Arc handle and write through it.**
   Requires changing the Value bridge so that when the interpreter sees an
   `out: [u8]` parameter (vs `in: [u8]`), it passes the underlying Arc and
   exposes a write-back path. Largest blast radius; safest semantics.
2. **Audit + delete all `_out`-discarding externs** and re-implement them as
   return-style. Lowest blast radius; matches the AES fix pattern.
3. **Detect `_out: [u8]` discards at extern-registration time** and refuse
   to dispatch in interpreter mode (loud failure beats silent corruption).

## Repro (reproduce after the AES fast-path workaround is removed)

```spl
extern fn rt_aes128_encrypt_block_into(key: [u8], block: [u8], out: [u8]) -> i64

fn _zeros(n: u64) -> [u8]:
    var out: [u8] = []
    var i: u64 = 0
    while i < n:
        out.push(0x00)
        i = i + 1
    out

fn main() -> i64:
    val key = _zeros(16u64)
    var output: [u8] = _zeros(16u64)
    val rc = rt_aes128_encrypt_block_into(key, key, output)
    # rc=0 (success) but output is still all zeros
    # Expected per FIPS 197: 66e94bd4ef8a2c3b884cfa59ca342b2e
    return 0
```

## Cross-refs

- T21 / T3 framing in `aes128_gcm_decrypt_string_to_int_2026-05-01.md`
  (refined fix landed; this doc is the latent FFI class behind it).
- `feedback_bug_doc_fixes_are_guesses.md` — verify before fixing.
