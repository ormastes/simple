# q35 Freestanding Filesystem DirectIo Driver Link Crash

Status: resolved by freestanding extent harness

## Summary

The standalone `x86_64-q35-pure-nvme-perf` boot lane passes when it measures the
pure NVMe lease adapter directly. A local attempt to instantiate the stdlib
`FsFat32Driver`, `NvfsDriver`, and `DbFsDriver` inside
`src/os/services/vfs/q35_pure_nvme_perf_boot.spl` caused the freestanding image
to fault before the NVMe probe logs were emitted.

This crash mode is no longer on the production q35 proof path. The q35 lane now
keeps hosted filesystem drivers out of the tiny freestanding image and instead
uses a freestanding-safe extent harness:

- FAT32 maps `/SYS/PERF/FAT4K.BIN` through the generated FAT fixture geometry
  and FAT chain.
- NVFS and DBFS map through their shared DBFS arena DirectIo formula
  (`arena_base + 1 + file_offset/io_unit`).
- The q35 catalog requires the serial markers
  `fat32_extent_source=freestanding-fat32-extents`,
  `nvfs_extent_source=freestanding-dbfs-arena`, and
  `dbfs_extent_source=freestanding-dbfs-arena`.

## Reproduction

The failing local patch imported the stdlib filesystem drivers into
`q35_pure_nvme_perf_boot.spl`, constructed them over a shared `NvmeBlockAdapter`,
mapped batches through `driver.direct_io_extent_for_handle(...)`, and submitted
the mapped offsets through `adapter.submit_direct_4k_shared_dma_batch(...)`.

Command:

```bash
src/compiler_rust/target/debug/simple os test --scenario x86_64-q35-pure-nvme-perf
```

Observed serial output started with:

```text
[BOOT32] entry
[BOOT64] entry
[BOOT64] idt
[BOOT64] call _start
[BOOT] _start entered
[BOOT] spl_start dispatch
4
=== SimpleOS q35 pure NVMe perf ===

[boot] memory init OK
FAULT @ 0x00000000001764f5
FAULT @ 0x00000000001764fa
FAULT @ 0x0500000012000000
...
```

The lane then timed out without the required `storage_provider=simple-driver`
or `nvme_perf reason=ready` markers.

## Historical Impact

This blocks using the standalone q35 perf lane as proof that FAT32, NVFS, and
DBFS DirectIo are exercised through their concrete filesystem driver instances.
Current passing evidence still proves the lower pure-Simple NVMe adapter path
and unit-level filesystem DirectIo extent mapping, but not full freestanding
filesystem-driver measurement in that tiny boot image.

## Resolution Evidence

The replacement proof path was added in:

- `2ab08b0468 test: prove q35 fat direct extents`
- `3286bc837d test: prove q35 nvfs dbfs direct extents`

Verification command:

```bash
src/compiler_rust/target/debug/simple os test --scenario x86_64-q35-pure-nvme-perf
```

Observed passing serial markers include:

```text
nvme_perf reason=ready ... direct_io_path=nvme-lease-shared-dma-4k fs_consumers=fat32,nvfs,dbfs fat32_extent_source=freestanding-fat32-extents nvfs_extent_source=freestanding-dbfs-arena dbfs_extent_source=freestanding-dbfs-arena c_bridge_used=false
TEST PASSED
```

The original linked hosted-driver crash remains useful as a caution: do not pull
`FsFat32Driver`, `NvfsDriver`, or `DbFsDriver` constructors into this q35 proof
lane unless the freestanding initializer/runtime issue is separately fixed.
