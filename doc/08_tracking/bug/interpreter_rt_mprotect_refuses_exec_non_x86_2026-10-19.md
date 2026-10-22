# Interpreter `rt_mprotect` refuses PROT_EXEC on non-x86 hosts (blocks dynSMF end-to-end on aarch64)

- Status: open
- Found: 2026-10-19, lane work/dynsmf-call-bytes
- Binary: Rust seed `simple-phase3-codec-candidate-20261018/.../target/bootstrap/simple`, sha256 prefix `9c45d2bf601ab93e`, aarch64 Linux host

## Repro

```simple
extern fn rt_mmap_raw(addr: i64, length: i64, prot: i64, flags: i64, fd: i64, offset: i64) -> i64
extern fn rt_mprotect(addr: i64, length: i64, prot: i64) -> i64
fn main():
    val a = rt_mmap_raw(0, 4096, 3, 0x22, -1, 0)
    print "rx=" + rt_mprotect(a, 4096, 5).to_text()
main()
```

Prints `rx=-1` with `SIMPLE_EXECUTION_MODE=interpreter`, and also with `=jit`.
Expected `rx=0`.

## Location

`src/compiler_rust/compiler/src/interpreter_extern/memory.rs:1111-1116`: under
`#[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]` any request
with `PROT_EXEC` returns -1 ("No verified cross-platform cache-sync primitive
exists in this lane"). Surfaces at `src/compiler/99.loader/segment_mapper.spl:439`
as `Failed to restore RX on segment dynsmf-handle-<n>#0`.

## Impact

On aarch64 (and every non-x86 host) the interpreter cannot map executable SMF
code, so `smf_dlopen_admitted` fails for every executable artifact: dynSMF
load + symbol resolve + call through `call_bytes_fn_v1` cannot run end to end.
`test/01_unit/os/smf/dynsmf_call_bytes_spec.spl` asserts that the loader fails
safely there instead of running the call.

Fix direction: an icache sync before granting RX (e.g. `__clear_cache` /
`sys_icache_invalidate` over the range) instead of refusing the request.
