# FAT32 Microbenchmark JIT Mutation-Capability Blocker

Date: 2026-05-27

## Summary

`bin/simple run test/perf/bench/fat32_microbench.spl` does not complete after
the FAT32 shared-core optimization work.

The first blockers were removed:

- `Result.Ok(...)` / `Result.Err(...)` static-member sugar in the FAT benchmark
  dependency slice blocked HIR lowering.
- The benchmark's nested `[[[u8]]]` sector bank crashed native execution before
  FAT code ran; it was replaced with flat byte storage.
- FAT cache writes that used `Dict.set(...)` crashed under JIT dispatch; the
  hot FAT cache paths now use dictionary index assignment.

Current native execution reaches the write workload and then segfaults before
entering `Fat32Core.write`. With `SIMPLE_DEBUG_METHOD_DISPATCH=1`, the compiler
reports several bare method calls in the FAT block-device path with `receiver ty
= Any`, including `read_sector`, `write_sector`, `sector_size`, and `get`.

Update 2026-05-28: the native HIR lowering blockers for exact enum static
constructor syntax (`Result.Err(...)` and `FsError.Transient(...)`) were cleared
for this path. The rebuilt compiler now reaches the memory-capability gate and
falls back with `Memory safety error [W1006]: mutation without mut capability`.
The remaining blocker is the trait/capability mutation analysis, not enum
constructor lowering.

## Reproduce

```bash
src/compiler_rust/target/debug/simple test/perf/bench/fat32_microbench.spl
```

## Current Status

- `bin/simple check` passes for the sync and async FAT fs-driver files.
- `bin/simple check test/perf/bench/fat32_microbench.spl --mode=interpreter`
  passes.
- Native execution prints the file-create result, then segfaults during the
  first write workload.

## Expected

The FAT32 microbenchmark should run under JIT, or the fallback interpreter
should handle the trait `self` usage correctly enough to complete the benchmark.

## Notes

The benchmark imports `std.fs_driver.fat32_core`, which resolves to the sync
stdlib FAT core used by the SimpleOS FAT adapter. Fixing this blocker is
required before claiming final 4K random read/write perf parity or superiority.
