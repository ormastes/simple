# Pure-Simple value/memory probe dict-entries failure — 2026-07-19

**Status:** SOURCE FIXED / RUNTIME QUALIFICATION PENDING

## Reproduction

```sh
cd src/compiler_rust
cargo test -p simple-compiler pipeline::native_project::tests::test_simple_core_source_tree_emits_partial_runtime_archive -- --exact
```

The pure-Simple archive builds, passes its required-symbol admission, and
passes the new `rt_string_trim_start` behavior check placed before dictionary
probing. The executable then exits `91` at the existing `rt_dict_entries`
row-shape assertion.

## Root cause and fix

The failing owner is the shared `rt_tuple_new` constructor in
`src/runtime/simple_core/core_array.spl`, not `core_values.spl` or the local
`rt_dict_entries` caller. `rt_tuple_new` now validates the allocated array and
nonnegative length, then sets the length directly. `rt_dict_entries` retains
the standard `rt_tuple_new(2)` / `rt_tuple_set` row ABI.

Retain the existing exact archive probe and require it to pass the exit-91
assertion before closing this report. This change has not run that Rust/archive
qualification here.
