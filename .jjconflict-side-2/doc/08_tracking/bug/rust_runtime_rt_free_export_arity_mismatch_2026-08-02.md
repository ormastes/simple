# Rust runtime `rt_free` export arity mismatch

- **ID:** `rust_runtime_rt_free_export_arity_mismatch_2026-08-02`
- **Status:** FIXED — claimed and repaired by `pure_parser_close` on 2026-08-02
- **Severity:** High (JIT runtime-symbol ABI / undefined behavior)

## Reproduction

Codegen declares `rt_free` with one `i64` argument and `elf_utils.rs` publishes
`simple_runtime::rt_free` at that symbol address. The Rust wrapper nevertheless
accepted `(ptr, size)`, even though its C callee and all runtime declarations
accept only the pointer. No Rust caller supplies the stale size argument.

## Scope

The pure Simple and SimpleOS boundaries were repaired first. This follow-up
restores Rust seed/native parity without changing allocator ownership or the
compiled-GC wiring lane.

## Fix and verification

The Rust wrapper now accepts only the pointer. A unit test assigns it to the
exact `fn(*mut u8)` type and exercises the adjacent null-free contract, while
the existing codegen declaration remains `rt_free(i64) -> ()`.
