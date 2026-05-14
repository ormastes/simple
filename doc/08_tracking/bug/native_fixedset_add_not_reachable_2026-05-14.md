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
- `native-build --source src/lib --entry test/perf/collections/collection_simple.spl --entry-closure ...`
  currently panics in native codegen before it can provide a source-closure
  workaround.

## Impact

This blocks using the existing pure Simple noalloc `FixedSet` as a verified
high-speed collection parity path in `test/perf/collections`.

## Expected Fix

Imported noalloc collection methods such as `FixedSet.add` and `FixedMap.put`
should be reachable in native builds that compile an entry importing those
modules, or the compiler should fail during compile/check with a precise
missing-method diagnostic instead of producing a crashing binary.
