# Native FixedSet.add Not Reachable From Collection Benchmark

Status: open
Date: 2026-05-14
Area: native compiler, noalloc collections

## Summary

Importing `std.nogc_async_mut_noalloc.collections.fixed_set.FixedSet` from
`test/perf/collections/collection_simple.spl` typechecks and compiles with
`simple compile --native`, but the resulting binary reports
`Runtime error: Function 'add' not found` for `set.add(...)` and eventually
segfaults.

## Reproduction

The failing benchmark variant used:

```spl
use std.nogc_async_mut_noalloc.collections.fixed_set.FixedSet

fn make_fixed_set() -> FixedSet:
    var set = FixedSet.new(2048)
    set.add(7)
    set
```

Validation observed:

- `SIMPLE_NO_STUB_FALLBACK=1 ./src/compiler_rust/target/debug/simple check ...`
  passes.
- `./src/compiler_rust/target/debug/simple compile test/perf/collections/collection_simple.spl --native --cpu native --opt-level aggressive ...`
  produces a binary.
- Running that binary emits repeated `Runtime error: Function 'add' not found`
  and exits with a segmentation fault.
- Before the runtime symbol declaration fix in `common_backend.rs`,
  `native-build --source src/lib --entry test/perf/collections/collection_simple.spl --entry-closure ...`
  panicked in native codegen while compiling generated collection runtime calls
  such as `rt_index_get`.
- After that fix, the same source-closure build completes, but it still emits
  stubs for required collection/runtime symbols such as
  `rt_array_new_with_cap_u64`, `rt_array_data_ptr`, and
  `rt_typed_words_u64_raw_data_at`; running the binary still dumps core.

## Impact

This blocks using the existing pure Simple noalloc `FixedSet` as a verified
high-speed collection parity path in `test/perf/collections`.

## Expected Fix

Imported noalloc collection methods such as `FixedSet.add` and `FixedMap.put`
should be reachable in native builds that compile an entry importing those
modules, and source-closure builds should either link the required collection
runtime symbols or fail during build with a precise unresolved-runtime
diagnostic instead of producing a crashing binary.
