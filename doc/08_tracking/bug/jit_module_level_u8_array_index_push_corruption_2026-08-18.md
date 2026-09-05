# Codegen (JIT) lane: module-level `val [u8]` indexed then `.push()`-ed reads back corrupted

**Date:** 2026-08-18
**Status:** OPEN — real correctness bug, worked around at the call site (not fixed in the compiler)
**Binary used:** `bin/release/x86_64-unknown-linux-gnu/simple` (Rust bootstrap
seed), 59620392 bytes, mtime 2026-08-18 01:08:42. `readlink -f bin/simple`
resolved to this path at measurement time.

## Summary

Found while fixing C-MIG-0023 (base64url perf,
`doc/08_tracking/bug/codegen_lane_still_slow_base64url_utf8_time_utils_2026-08-18.md`
finding 1). Encoding `base64url_encode("f")` under `SIMPLE_JIT_STRICT=1`
produced garbage (`и`, then `Ш?`, `ШȰ`, `ШȰȨ0?` for progressively longer
inputs) instead of the correct `Zg`/`Zm8`/`Zm9v`/`Zm9vYmFy`, while
`bin/simple test` (tree-walk interpreter) produced correct output for the
same source. The difference was isolated to a single construct.

## Minimal repro

```
val TABLE = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
val TBYTES = TABLE.bytes()

fn main():
    var out: [u8] = []
    val x = TBYTES[0]
    print("x={x}")          # -> 65 (correct, 'A')
    out = out.push(x)
    print("after push x: {out[0]}")   # -> 8 (WRONG, should be 65)
main()
```

Run with `SIMPLE_JIT_STRICT=1 bin/simple run <file>`.

## Isolation (all under `SIMPLE_JIT_STRICT=1`, same binary)

- `TBYTES[0]` read directly (no push): **65, correct.**
- `x = TBYTES[0]; out.push(x)` then read `out[0]`: **8, wrong.**
- Same but `TBYTES` computed as a **function-local** `val local_bytes =
  TABLE.bytes()` instead of module-level: **65, correct.**
- `out.push(65u8)` (literal, no array involved): **65, correct.**
- `var arr: [u8] = [65u8, 97u8]; out.push(arr[0])` with `arr` local: **65,
  correct.**
- Same with `arr[idx]` where `idx` is a local `i64` var: **65, correct.**

So the defect is specific to: value sourced from indexing a **module-level**
`val [u8]` array, then passed through `.push()` into another `[u8]` array.
Direct reads of the module-level array are fine; local arrays of identical
shape and the same push pattern are fine. Only the combination
(module-level source + push-elsewhere) corrupts.

`65 -> 8`: note `65 >> 3 == 8`, suggestive of some tag/representation bit
loss on the value as it crosses from a module-level-array element into the
`.push()` call under JIT, but the exact codegen mechanism was not
investigated further (out of scope for the perf task that found this).

## Impact / workaround

`src/lib/common/base_encoding/base64.spl` originally hoisted
`ENCODE_BYTES = ENCODE_TABLE.bytes()` to module scope as part of a perf fix
(byte-array accumulation instead of scalar text concatenation) and hit
exactly this bug. Workaround applied: compute the encode-table bytes as a
**function-local** (`val encode_bytes = ENCODE_TABLE.bytes()` inside
`_base64_encode_bytes`) instead of a module-level `val`. This produces
correct output under both the interpreter and the JIT lane, verified by the
100-vector shared-corpus differential spec
(`test/01_unit/lib/common/base_encoding/base64/base64url_crosslang_spec.spl`,
7/7 passed) plus a direct `SIMPLE_JIT_STRICT=1 bin/simple run` smoke check of
`base64url_encode` on the RFC 4648 KAT vectors.

Any other module-level `val [u8]`/`[i64]`/etc. array read via `arr[i]` and
then `.push()`-ed into a different array under the codegen lane should be
treated as suspect until this is root-caused and fixed in the compiler.

## Non-actions taken here

No compiler source change was made — this was found and worked around while
doing library-level perf work, not a compiler-focused task. Filing this so
whoever owns Cranelift JIT array/module-scope codegen can pick it up.
