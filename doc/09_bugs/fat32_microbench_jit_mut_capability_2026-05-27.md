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

Update 2026-05-28 (later): the perf benchmarks no longer depend on interpreter
SFFI pointer-style byte buffer mutation for their fake disk image; they use
ordinary pure Simple `[u8]` push/index assignment so the same source is shared
with native lowering. The native C runtime byte-array `rt_array_set` path now
normalizes tagged numeric values before storing into packed byte arrays. A
native-build of `fat32_microbench.spl` links and no longer segfaults, but FAT
mount still fails with `FAT32 boot sector must be at least 512 bytes`, which
points at the known `BlockDevice` trait dispatch path returning the wrong
`sector_size()`. A MIR lowering patch now gates virtual trait dispatch on the
recovered receiver type instead of the original `Any` receiver type; it still
needs verification with a rebuilt driver once unrelated networking worktree
changes stop blocking `cargo build -p simple-driver`.

Update 2026-05-28 (native weak-stub blocker): `cargo build -p simple-driver`
now succeeds, and native-build links the benchmark without segfaulting. The
mount failure was not a real FAT geometry result. Disassembly showed
`Fat32Core._device_sector_size` calling the generated weak stub
`fat32_microbench__BenchBlockDevice_dot_sector_size`, which returned nil, while
the real benchmark method was emitted as the module-qualified symbol
`home__ormastes__dev__pub__simple__test__perf__bench__fat32_microbench__BenchBlockDevice_dot_sector_size`.
The hosted native stub generator now emits a weak jump trampoline when an
unresolved short Simple symbol has exactly one defined module-qualified symbol
with the same `Type_dot_method` tail. After that change, the native
`fat32_microbench.spl` completes all workloads.

Update 2026-05-28 (4K comparison): `fat32_4k_compare.spl` native-builds, but
the resulting binary still reports `FATAL: simple read failed` and
`FATAL: simple write failed`, then times out before producing a valid comparison
result. This means the pure Simple FAT microbenchmark is unblocked, but the 4K
random read/write superiority claim is not verified yet.

## Reproduce

```bash
src/compiler_rust/target/debug/simple test/perf/bench/fat32_microbench.spl
```

## Current Status

- `bin/simple check` passes for the sync and async FAT fs-driver files.
- `bin/simple check test/perf/bench/fat32_microbench.spl --mode=interpreter`
  passes.
- Native `fat32_microbench.spl` completes all workloads.
- Native `fat32_4k_compare.spl` builds but the simple read/write comparison
  path still fails and times out.

## Expected

The FAT32 microbenchmark should run under JIT, or the fallback interpreter
should handle the trait `self` usage correctly enough to complete the benchmark.

## Notes

The benchmark imports `std.fs_driver.fat32_core`, which resolves to the sync
stdlib FAT core used by the SimpleOS FAT adapter. Fixing this blocker is
required before claiming final 4K random read/write perf parity or superiority.
