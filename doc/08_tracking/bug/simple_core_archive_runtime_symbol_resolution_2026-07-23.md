# Bug: simple-core archive local runtime symbol resolution — 2026-07-23

**Status:** SOURCE FIXED / ARCHIVE QUALIFICATION PENDING

## Reproduction

```sh
cd src/compiler_rust
cargo test -p simple-compiler pipeline::native_project::tests::test_simple_core_source_tree_emits_partial_runtime_archive -- --exact
```

Before this fix, `core_string.spl` compilation panics in
`rt_native_eq_inner` with `missing runtime fn 'rt_native_neq'`.

## Root cause and fix

The exact simple-core archive path can define `rt_native_neq` locally while a
generated `NotEq` still calls the shared runtime helper. That helper previously
looked only in `runtime_funcs` and panicked even though the local function was
already declared in `func_ids`.

`call_runtime_*` now prefers a local declaration and falls back to the runtime
import. A focused Rust regression compiles generated `NotEq` over `ANY` values
with a locally defined `rt_native_neq`, asserting that no runtime import is used.

This does not prove the archive passes. Keep the existing exact archive probe
as the qualification gate, and track its independent tuple-row failure in
[`simple_core_value_memory_probe_dict_entries_failure_2026-07-19.md`](simple_core_value_memory_probe_dict_entries_failure_2026-07-19.md).
