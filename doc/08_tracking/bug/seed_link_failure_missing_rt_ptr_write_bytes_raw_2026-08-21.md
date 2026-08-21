# Seed fails to LINK: undefined symbol `rt_ptr_write_bytes_raw`

Date: 2026-08-21
Status: RESOLVED 2026-08-21 — C definition added; `cargo build --release --bin simple` rc=0
Severity: critical (the Rust seed could not be built at all)

## Symptom

```
$ CARGO_TARGET_DIR=/mnt/data/.cargo-target-sffi cargo build --release --bin simple -j8
rust-lld: error: undefined symbol: rt_ptr_write_bytes_raw
>>> referenced by simple_runtime::value::sffi::memory::rt_ptr_write_bytes_raw_shim
>>>               in archive .../libsimple_runtime.rlib
error: could not compile `simple-driver` (bin "simple")   (rc=101)
```

## Root cause

`src/compiler_rust/runtime/src/value/sffi/memory.rs:17` declares
`rt_ptr_write_bytes_raw` in its `c_sffi` extern block, and the comment at `:67`
asserts "NOT `#[no_mangle]`: the C runtime already exports
`rt_ptr_write_bytes_raw`". It did not: no `.c` or `.h` under `src/runtime/`
defined or declared that name anywhere. The sibling primitives
(`rt_ptr_write_u8` / `_i32` / `_i64`) are all in
`src/runtime/runtime_memory.c`; this one was never written.

This is exactly the defect class of
`check-no-unresolved-runtime-symbols.shs` — a codegen/shim-emitted runtime entry
with no definition in the C runtime archive — except that here the reference was
strong enough to break the LINK rather than survive to a NULL-jump at runtime.
`-fsyntax-only` (the C-runtime compile guard) cannot see it, since it never
links.

## Fix

`src/runtime/runtime_memory.c` — define it next to the other `rt_ptr_write_*`
primitives, with the same rejection rule the Rust shim already applies
(`addr == 0 || src == NULL || offset < 0 || len <= 0` -> 0), returning the byte
count written.

## Reproduce / gate

The build itself is the test, and it is fail-closed: reverting the C definition
reproduces the exact `rust-lld: error: undefined symbol` above. Verified in both
directions on this host — rc=101 before, rc=0 after (binary 59,971,528 bytes,
2026-08-21 14:53).
