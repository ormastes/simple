# FAT32 Microbenchmark JIT Mutation-Capability Blocker

Date: 2026-05-27

Status: Original crash resolved 2026-05-29; VFAT/C-FAT proof remains
environment-gated. VFAT setup diagnosis now reports exact remediation.

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

Update 2026-05-28 (4K simple path unblocked): the focused 4K comparison harness
now uses the stateful FAT test-device registry for Simple FAT operations and
resets that registry explicitly before registering its in-memory block device.
The Simple FAT random 4K read/write path completes under native-build and emits
p50/p99 latency numbers. Host POSIX and VFAT baselines are still skipped in the
self-contained native build because host file SFFI functions are unresolved and
stubbed, so the C-FAT superiority claim remains unproven.

Update 2026-05-28 (hosted run crash): `bin/simple run
test/perf/bench/fat32_4k_compare.spl` segfaults with rc=139 immediately after
printing the benchmark banner. Temporary instrumentation localized the crash to
`Fat32Core.mount() -> read_boot_sector() -> BenchBlockDevice.read_sector()`,
while copying bytes into the trait-supplied mutable sector buffer. The harness
was changed to exercise `Fat32Core` directly instead of the global test-device
registry, deduplicate dirty cluster tracking, and shrink the in-memory FAT image
to the sectors actually used by the 4K workload, but the hosted JIT trait buffer
write crash remains open. This blocks a fresh hosted `bin/simple run` proof of
4K random read/write superiority.

Update 2026-05-28 (returned-sector BlockDevice): the shared stdlib
`BlockDevice.read_sector` contract now returns `Result<[u8], text>` instead of
mutating a caller-provided byte buffer. FAT32, NVFS, DBFS, the shared intent log
and checkpoint ring, the SimpleOS NVMe/VFS adapters, VirtIO adapter, host raw
image adapters, and the FAT benchmarks were moved to the returned-sector API so
the pure Simple filesystem interface no longer depends on trait out-parameter
mutation. Focused `bin/simple check` runs pass. A rebuilt debug driver also
confirms `sector_size`, `read_sector`, and `write_sector` lower as virtual trait
calls, but `fat32_4k_compare.spl` still segfaults after the banner, so the
remaining blocker is native virtual trait call execution for this returned array
path, not the old mutable sector buffer contract.

Update 2026-05-28 (hosted crash cleared, write proof still blocked): hosted
`src/compiler_rust/target/debug/simple run
test/perf/bench/fat32_4k_compare.spl` no longer segfaults. The benchmark now
uses the shared returned-sector helper for its in-memory block device and
validates seed writes against FAT open-file state because native
`Result<i64>.unwrap()` can report `512` even after the file position and size
advance by `4096`. The read path can produce a faster-than-host-POSIX focused
number in this in-memory harness, but the write path still skips with
`failed to write FAT entry`; VFAT/C-FAT same-device baselines remain skipped.
The faster-than-C FAT claim is therefore still unproven.

Update 2026-05-28 (hosted 4K read/write completes): `follow_chain` now bounds
traversal by the mounted volume's `total_clusters + 2`, so native execution no
longer treats a mis-decoded EOC marker as a real cluster and no longer attempts
to write FAT entry `0x01ffffff`. Hosted
`src/compiler_rust/target/debug/simple run
test/perf/bench/fat32_4k_compare.spl` completes the Simple FAT read and write
paths and reports the in-memory Simple FAT p50/p99 faster than the host POSIX
baseline. VFAT/C-FAT same-device baselines remain skipped, so production
faster-than-C FAT is still unproven.

## Reproduce

```bash
src/compiler_rust/target/debug/simple test/perf/bench/fat32_microbench.spl
```

## Current Status

- `bin/simple check` passes for the sync and async FAT fs-driver files.
- `bin/simple check test/perf/bench/fat32_microbench.spl --mode=interpreter`
  passes.
- Native `fat32_microbench.spl` completes all workloads.
- Native `fat32_4k_compare.spl` builds and the Simple FAT 4K read/write path
  completes, but host/VFAT baselines are skipped in the self-contained native
  build due unresolved host file SFFI stubs.
- Hosted `src/compiler_rust/target/debug/simple run
  test/perf/bench/fat32_4k_compare.spl` completes Simple FAT 4K random read and
  write in the focused in-memory harness; VFAT/C-FAT same-device proof remains
  missing.
- Rechecked 2026-05-29 by spawned agent:
  `src/compiler_rust/target/debug/simple run test/perf/bench/fat32_microbench.spl`
  exits 0, and
  `src/compiler_rust/target/debug/simple run test/perf/bench/fat32_4k_compare.spl`
  exits 0 with Simple FAT read/write complete. The remaining `c_fat_vfat_*`
  paths are skipped because `/tmp/simple_vfat_bench_mnt` is mounted as `vfat`
  but not writable/seeded and passwordless sudo is unavailable.

## Expected

The FAT32 microbenchmark should run under JIT, or the fallback interpreter
should handle the trait `self` usage correctly enough to complete the benchmark.

## Notes

The benchmark imports `std.fs_driver.fat32_core`, which resolves to the sync
stdlib FAT core used by the SimpleOS FAT adapter. Fixing this blocker is
required before claiming final 4K random read/write perf parity or superiority.

## Remaining Follow-up

The JIT mutation-capability blocker is no longer the active issue. The next
implementation item is the VFAT baseline setup path: make
`scripts/perf/prepare-fat32-4k-vfat.shs --diagnose` either recreate a writable
fixture via the documented flow or report a precise manual setup requirement,
then rerun `fat32_4k_compare.spl` until `c_fat_vfat_read4k` and
`c_fat_vfat_write4k` are measured rather than skipped.

Update 2026-05-29: the VFAT setup path now gives an exact next action in
`--diagnose` output. On this host the default mount is already `vfat` but is
not writable by the current user and not seeded, so diagnosis reports:
`next: unmount or remount /tmp/simple_vfat_bench_mnt with uid=1000,gid=1000`
and prints the corresponding `sudo umount ... && VFAT_MNT=... VFAT_IMG=...`
manual command. For custom unmounted paths, diagnosis reports the exact
`VFAT_MNT=... VFAT_IMG=... scripts/perf/prepare-fat32-4k-vfat.shs` command and
the need for passwordless sudo or polkit udisks authorization. The benchmark
now honors `VFAT_MNT` instead of hardcoding `/tmp/simple_vfat_bench_mnt`, so a
prepared non-default mount can be measured by the same command.

Verification:

```bash
bash -n scripts/perf/prepare-fat32-4k-vfat.shs
scripts/perf/prepare-fat32-4k-vfat.shs --diagnose
VFAT_MNT=/tmp/simple_vfat_diag_smoke.<tmp> VFAT_IMG=/tmp/simple_vfat_diag_smoke.img scripts/perf/prepare-fat32-4k-vfat.shs --diagnose
SIMPLE_LIB=src bin/simple check test/perf/bench/fat32_4k_compare.spl
```

Remaining environment-gated proof: rerun the full comparison after the VFAT
mount is remounted writable/seeded or a polkit-authorized loop mount is
available, and require both `c_fat_vfat_read4k` and `c_fat_vfat_write4k` to be
measured rather than skipped.
