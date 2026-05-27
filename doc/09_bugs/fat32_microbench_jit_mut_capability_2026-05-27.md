# FAT32 Microbenchmark JIT Mutation-Capability Blocker

Date: 2026-05-27

## Summary

`bin/simple run test/perf/bench/fat32_microbench.spl` does not complete after
the FAT32 shared-core optimization work. The earlier JIT blockers from
`Result.Ok(...)` / `Result.Err(...)` static-member sugar in the FAT benchmark
dependency slice were removed, but JIT now stops with:

```text
HIR lowering error: Memory safety error [W1006]: mutation without mut capability: mutation requires `mut` capability
```

The fallback interpreter then exits with:

```text
error: semantic: variable `self` not found
```

## Reproduce

```bash
bin/simple run test/perf/bench/fat32_microbench.spl
```

## Current Status

- `bin/simple check` passes for the sync and async FAT fs-driver files.
- `bin/simple check test/perf/bench/fat32_microbench.spl --mode=interpreter`
  passes.
- Runtime execution remains blocked before benchmark numbers are produced.

## Expected

The FAT32 microbenchmark should run under JIT, or the fallback interpreter
should handle the trait `self` usage correctly enough to complete the benchmark.

## Notes

The benchmark imports `std.fs_driver.fat32_core`, which resolves to the sync
stdlib FAT core used by the SimpleOS FAT adapter. Fixing this blocker is
required before claiming final 4K random read/write perf parity or superiority.
