# q35 Freestanding Filesystem DirectIo Driver Link Crash

Status: open

## Summary

The standalone `x86_64-q35-pure-nvme-perf` boot lane passes when it measures the
pure NVMe lease adapter directly. A local attempt to instantiate the stdlib
`FsFat32Driver`, `NvfsDriver`, and `DbFsDriver` inside
`src/os/services/vfs/q35_pure_nvme_perf_boot.spl` caused the freestanding image
to fault before the NVMe probe logs were emitted.

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

## Impact

This blocks using the standalone q35 perf lane as proof that FAT32, NVFS, and
DBFS DirectIo are exercised through their concrete filesystem driver instances.
Current passing evidence still proves the lower pure-Simple NVMe adapter path
and unit-level filesystem DirectIo extent mapping, but not full freestanding
filesystem-driver measurement in that tiny boot image.

## Next Step

Split a freestanding-safe filesystem DirectIo harness from hosted stdlib driver
initialization, or identify the linked symbol/static initializer that makes the
standalone q35 image fault before NVMe probing.
