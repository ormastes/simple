# simple-driver Runtime Symbol Table Link Failure

Status: Verified resolved 2026-05-29. The `cargo build -q -p simple-driver --bin simple` build

Date: 2026-05-27

## Summary

Resolved. A fresh `simple-driver` build now succeeds after tightening runtime
symbol-table generation to real exported C ABI symbols.

## Evidence

Command:

```sh
cargo build -q --manifest-path src/compiler_rust/Cargo.toml -p simple-driver --bin simple
```

Previous result:

- fails while linking `simple`
- unresolved symbols include `sffi_regex_is_match`, `sffi_regex_find`,
  `sffi_regex_replace_all`, `rt_value_int`, `rt_value_float`, `rt_value_bool`,
  `rt_value_nil`, `rt_ptr_to_value`, `rt_value_to_ptr`,
  `rt_function_not_found`, and `rt_method_not_found`

## Impact

This no longer blocks startup-size verification. The audit can run with
`SIMPLE_BINARY=src/compiler_rust/target/debug/simple` to exercise current
compiler/linker sources.

## Cause

`src/compiler_rust/runtime/build.rs` generates runtime symbol table entries from
a broad text scan for `fn <symbol>`. Some symbols are Rust functions that are
not exported as C ABI symbols, while other symbol-table references are emitted
as extern references instead of direct Rust item references.

## Fix

`src/compiler_rust/runtime/build.rs` now only emits runtime symbol-table entries
for symbols with `#[no_mangle]` or matching `#[export_name = "..."]`, and skips
the disabled regex implementation when `runtime-regex` is not enabled.

Verification:

```sh
cargo build -q --manifest-path src/compiler_rust/Cargo.toml -p simple-driver --bin simple
```

## Status

Verified resolved 2026-05-29. The `cargo build -q -p simple-driver --bin simple` build
completes with warnings only (no linker errors). `rust_file_exports_symbol` and the
`runtime_regex` feature-gate are present in `build.rs` and the symbol-table entries
generated are limited to `#[no_mangle]` / `#[export_name]` C ABI symbols. No pure
Simple (.spl) equivalent exists for this Cargo build script; the fix is correctly
confined to `src/compiler_rust/runtime/build.rs`.
