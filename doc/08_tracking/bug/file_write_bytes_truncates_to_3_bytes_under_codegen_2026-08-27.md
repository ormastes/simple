# `file_write_bytes` writes 3 garbage bytes when the call is codegen-compiled

Date: 2026-08-27
Status: OPEN — root-caused and minimally reproduced; fix is in the Rust seed
        (`src/compiler_rust/`), out of scope for this lane.
Class: (b) real product bug — seed extern-argument marshalling
Found by: soak lane (reported, not fixed; it cost that lane real time by
          mimicking a gzip failure), reproduced and root-caused here.

## Symptom
A `bin/simple run` script reads 16 KB, calls `file_write_bytes`, and the output
file is **3 bytes**: `08 00 00`. No gzip is involved. `file_write_bytes` returns
`true`. The length is independent of the input: a 5-element `[u8]` literal and a
16384-element array both produce the same 3 bytes.

## Minimal reproduction
```simple
# lit4.spl
use std.io_runtime.{file_write_bytes}
fn main():
    val b: [u8] = [1u8, 2u8, 3u8, 4u8, 5u8]
    print("ok={file_write_bytes("/tmp/lit4.bin", b)}")
```
`bin/simple run lit4.spl` -> `ok=true`, and `/tmp/lit4.bin` is `08 00 00`.
Expected `01 02 03 04 05`.

## A/B that isolates it (same stdlib function, two engines)
| script | how it resolves | engine actually used | bytes written |
|---|---|---|---|
| `lit3.spl` — `use std.io_runtime` then `io_runtime.file_write_bytes(...)` | qualified call fails codegen (`GlobalLoad: unresolved identifier 'io_runtime'`) -> `CODEGEN-STUB-FALLBACK` -> interpreter | **interpreter** | `01 02 03 04 05` (CORRECT) |
| `lit4.spl` — `use std.io_runtime.{file_write_bytes}` | compiles; only a `hybrid-interp-splice` demotion, no compile failure | **codegen** | `08 00 00` (WRONG) |

Same function, same extern, same `[u8]` value. The only difference is whether
the call site was compiled or interpreted. The interpreter marshals the byte
array correctly; the codegen path does not.

The same wrong result appears through every other wrapper that reaches the
compiled path — `std.io.file_ops.file_write_bytes`, `std.sffi.io.file_write_bytes`,
and a locally declared `extern fn rt_file_write_bytes(path: text, data: [u8]) -> bool`
called directly. So it is not a wrapper bug: all of them are thin, identical
delegations to `rt_file_write_bytes`, and the C runtime implementation
(`src/runtime/runtime_native.c:12661`, `rt_file_write_bytes_array`) is correct
by inspection. The defect is in how the seed's compiled path passes a `[u8]`
argument to that extern.

Note: `SIMPLE_ENGINE`, `SIMPLE_JIT`, `SIMPLE_USE_JIT` and `SIMPLE_DISABLE_JIT`
do **not** switch engines on this binary — all four still produced `08 00 00`.
The interpreter evidence above comes from a genuine, logged codegen fallback,
not from an env var.

## Impact
Any `.spl` program that writes bytes through a compiled call site silently
produces a 3-byte file while reporting success. Silent data loss with a `true`
status is the worst shape this can take: callers that check the return value are
not protected.

Not currently hit by scv: `src/app/scv/main.spl` drops wholesale to the
interpreter (unresolved external symbol `spl_thread_current_id`), so scv's
`file_write_bytes` calls take the correct path today. That is luck, not design —
it changes the moment that symbol resolves.

## Fix
In the Rust seed's extern-call marshalling for array arguments. Not attempted
here: `src/compiler_rust/**` was explicitly out of scope for this lane.

## Regression test to add with the fix
The `lit3`/`lit4` pair above is the whole test: write N bytes, read the file
back, assert the size and content match, from a call site that is NOT forced
into the interpreter.
