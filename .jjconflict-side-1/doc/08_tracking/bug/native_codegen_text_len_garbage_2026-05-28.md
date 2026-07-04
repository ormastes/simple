# BUG: text.len() returns garbage value in native LLVM codegen

Status: FIXED (2026-05-29)

**Date:** 2026-05-28
**Status:** FIXED (2026-05-29)
**Severity:** High (all native-compiled code using text.len() affected)
**Component:** LLVM backend codegen — method dispatch on text type

## Problem

Calling `.len()` on a `text` value in native LLVM-compiled code returns garbage instead of the actual string length. Observed return value: `2305843009213693951` (0x1FFFFFFFFFFFFFFF) for a 13-byte string.

```
val body = rt_file_read_all_text(file_path)
val body_len = body.len()   # returns 2305843009213693951, should be 13
```

The same `.len()` call works correctly in interpreter mode.

## Root cause (confirmed)

The LLVM backend's inline `compile_inline_len` function in
`src/compiler_rust/compiler/src/codegen/llvm/functions/calls.rs` checks the first byte
at offset 0 of the heap object and compares to `1` for string detection. But:

- `RtCoreString.kind` is `uint32_t = 0x53545231U` ("STR1" magic). First byte on
  little-endian = `0x31` = 49, not 1. So string detection always fails.
- `RtCoreArray.kind` is `uint8_t = 0x02U`. First byte = 2. Array detection works. ✓

When string detection fails, the phi node in the inline code returns `invalid = -1`
(`0xFFFFFFFFFFFFFFFF`). When `print` calls `rt_print_value(-1)`, it decodes it as a
`RT_VALUE_TAG_SPECIAL` value and extracts payload `(-1 >> 3) = 0x1FFFFFFFFFFFFFFF =
2305843009213693951` — the garbage value observed.

The same bug existed in the Cranelift `inline_runtime_len_value` in
`src/compiler_rust/compiler/src/codegen/instr/helpers.rs`.

The same logic bug exists in the pure-Simple LLVM backend
(`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`) but that path is not currently used
by `native-build` (dispatches to Rust seed by default).

## Reproduction

```bash
mkdir -p /tmp/simple_bench_data
echo -n 'Hello, World!' > /tmp/simple_bench_data/hello.txt
```

```
extern fn rt_file_read_all_text(path: text) -> text
fn main():
    val body = rt_file_read_all_text("/tmp/simple_bench_data/hello.txt")
    print body.len()    # prints 2305843009213693951, expected 13
```

Build with: `bin/simple native-build --source <dir> --entry <file> -o output`

## Workaround

Use `extern fn rt_string_len(s: text) -> i64` directly instead of `.len()`:

```
extern fn rt_string_len(s: text) -> i64
val body_len = rt_string_len(body)   # correctly returns 13
```

## Impact

- All native-compiled code using `text.len()` gets wrong values
- Benchmark code (`bench_raw_tcp_static.spl`) uses `rt_string_len` workaround
- Any native HTTP server building Content-Length headers from `.len()` would send corrupt headers

## Fix

Changed `compile_inline_len` in both the LLVM and Cranelift backends to load the
`kind` field as `u32` (4 bytes) and compare to `RT_VALUE_HEAP_STRING = 0x53545231U`
for string detection, instead of loading `i8` and comparing to `1`.

Files changed:
- `src/compiler_rust/compiler/src/codegen/llvm/functions/calls.rs` — LLVM inline len
- `src/compiler_rust/compiler/src/codegen/instr/helpers.rs` — Cranelift inline len

Verified: `body.len()` returns 13 (correct), `arr.len()` returns 5 (no regression).
