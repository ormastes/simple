# Seed JIT: [0u8; n] copy-then-push leaks more than a push-built [u8] (2026-11-27)

Status: fix-implemented-verification-pending, P3. Seed: /home/yoon/.cache/cargo-target-wr-seed1126b/release/simple, SIMPLE_EXECUTION_MODE=jit.

## Repro
In `_pbkdf2_cat_u8(a, b)` (`var r: [u8] = a` then `r.push(b[i])`), pass `a` as a 64-byte pad built
with `[0u8; 64]` plus index stores. Run PBKDF2-HMAC-SHA256 for 20000 iterations: RSS is 172 MB. Build
the same pad with `push` instead and RSS is 131-137 MB. With 1 iteration both shapes use 94 MB.
Digests are identical.

## Root Cause
Dynamic `[0u8; n]` repeat literals (`HirExprKind::ArrayRepeat`) lowered in MIR (`lower_array_repeat_expr`) unconditionally to `rt_array_repeat(boxed_val, count)`, which allocates an unpacked 8-byte-per-element `RuntimeArray` instead of a byte-packed (`BYTE_PACKED`) array. Copying via `var r: [u8] = a` (`rt_array_copy`) preserved the unpacked representation, and `r.push(...)` reallocated an 8x-larger unpacked backing buffer (1024 B vs 128 B per call for 64->128 capacity growth). In addition, `lowering_stmt.rs` early returns for `is_u8_array_declared` `HirExprKind::Array` bypassed `block_release_ready` registration for S1 block-end `rt_array_free`.

## Fix
- Route `[u8]` / `u8`-repeat MIR lowering (`lowering_expr_collection.rs`, `lowering_stmt.rs`, `lowering_expr.rs`, `lowering_core.rs`) through `lower_u8_array_repeat_expr` using `rt_byte_array_new_len` (+ `rt_array_fill_span` for non-zero byte fills, re-exported in `runtime/src/value/mod.rs` and `compiler/src/elf_utils.rs`) when `!self.array_push_returns_header`.
- Register `block_release_ready` and len/capacity locals before `is_u8_array_declared` early returns in `lowering_stmt.rs`.

## Workaround
`_pbkdf2_u8_pad` in `src/lib/common/crypto/pbkdf2.spl` builds the pad with push
(`@workaround(jit_u8_repeat_literal_copy_push_leak_2026-11-27)`). Retiring this `@workaround` in `src/lib/common/crypto/pbkdf2.spl` stays deferred to `pbkdf1`/follow-up because `pbkdf2.spl` is concurrently owned.
