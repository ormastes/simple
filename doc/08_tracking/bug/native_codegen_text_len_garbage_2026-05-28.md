# BUG: text.len() returns garbage value in native LLVM codegen

**Date:** 2026-05-28
**Status:** OPEN
**Severity:** High (all native-compiled code using text.len() affected)
**Component:** LLVM backend codegen — method dispatch on text type

## Problem

Calling `.len()` on a `text` value in native LLVM-compiled code returns garbage instead of the actual string length. Observed return value: `2305843009213693951` (0x1FFFFFFFFFFFFFFF) for a 13-byte string.

```
val body = rt_file_read_all_text(file_path)
val body_len = body.len()   # returns 2305843009213693951, should be 13
```

The same `.len()` call works correctly in interpreter mode.

## Root cause (suspected)

The native codegen method dispatch for `.len()` on tagged text values likely:
1. Does not untag the heap pointer before accessing the RtCoreString struct, OR
2. Reads from wrong offset (e.g., reading the tag bits or capacity field instead of len), OR
3. The method lookup resolves to the wrong implementation (array.len vs string.len)

Tagged text values use `ptr | 0x1` encoding. The `len` field is at `RtCoreString->len`. The `rt_string_len()` C extern correctly untags and reads `s->len`.

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
