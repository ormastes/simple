# Pure-Simple value/memory probe dict-entries failure — 2026-07-19

**Status:** REPRODUCED / OPEN

## Reproduction

```sh
cd src/compiler_rust
cargo test -p simple-compiler pipeline::native_project::tests::test_simple_core_source_tree_emits_partial_runtime_archive -- --exact
```

The pure-Simple archive builds, passes its required-symbol admission, and
passes the new `rt_string_trim_start` behavior check placed before dictionary
probing. The executable then exits `91` at the existing `rt_dict_entries`
row-shape assertion.

## Next smallest action

Trace `core_values.spl` dictionary-entry construction against the two-element
row ABI. Fix that owner and retain the existing probe; do not weaken or skip the
assertion.
