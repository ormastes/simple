# SimpleOS NVMe/FAT Production Restart Plan — 2026-05-28

## Current State

- NVMe storage model has explicit system/user namespace modes, queue roles, and
  FAT32/NVFS/DBFS shared lease contracts.
- VFS production boot routes through pure-Simple NVMe handoff and rejects C
  bridge/virtio production fallback paths.
- Raw NVMe namespace queue access is guarded so system and user data queues
  cannot use the same namespace at the same time.
- FAT32 production VFS and boot paths are guarded to stay on the shared pure
  Simple FAT core (`SharedFat32Driver` / `FsFat32Driver`), not legacy
  `os.services.fat32.Fat32Driver`.
- Pure boot VFS read/exec/size/exists paths gate off transitional
  `simpleos_fat32_*` C bridge fallbacks.
- Real-hardware NVMe performance acceptance requires explicit physical-device
  identity and repeated physical runs.

## Known Remaining Work

1. Prove the physical NVMe production lane on real hardware.
   - Run `scripts/run_simpleos_physical_nvme_perf.shs --production --serial-log <path>`.
   - Verify the log with `src/app/simpleos_nvme_serial_check/main.spl`.
   - Required evidence includes `hardware_target=real-nvme`, `qemu=false`,
     `physical_runs>=3`, direct 4K shared-DMA paths, FAT32/NVFS/DBFS consumer
     markers, and same-device C/VFAT comparison fields.

2. Fix the serial checker runtime crash before treating app-level evidence as
   production-grade.
   - Recent failure path showed native/codegen crash around `file_modified_time`
     with exit code 139.
   - Core parser contracts passed, but the app spec did not.

3. Retire duplicate legacy FAT implementation safely.
   - Keep production guard in place.
   - Move hardening helpers (`Fat32Bpb`, `validate_bpb`,
     `detect_cluster_cycle`) out of legacy `os.services.fat32.fat32` into the
     shared stdlib FAT area.
   - Migrate remaining tests/tools that directly instantiate
     `Fat32Driver.new(...)`, then mark/delete legacy FAT files.
   - Host FAT image populator still uses the legacy driver because direct
     migration to `Fat32Core` exposed nested-directory persistence differences.

4. Finish performance proof for Simple FAT vs C/VFAT on 4K random read/write.
   - Keep `scripts/perf/run-fat32-4k-cfat-baseline.shs` as the focused gate.
   - Require VFAT baseline when making the stronger “faster than C FAT” claim.
   - Record median/p50/p99 evidence, not single-sample claims.

5. Audit direct I/O for all three filesystem consumers.
   - FAT32 is wired through shared FAT extents.
   - NVFS/DBFS direct I/O markers exist, but real hardware proof must show the
     same NVMe adapter and lease-backed queue path for all consumers.

## Suggested Restart Commands

```bash
bin/simple test test/unit/os/services/vfs/vfs_pure_fat_production_guard_spec.spl --mode=interpreter --clean
bin/simple test test/unit/os/services/vfs/vfs_boot_nvme_lease_spec.spl --mode=interpreter --clean
bin/simple test test/unit/os/drivers/nvme/nvme_driver_probe_contract_spec.spl --mode=interpreter --clean
bin/simple test test/unit/os/drivers/nvme/nvme_performance_contract_spec.spl --mode=interpreter --clean
bin/simple test test/unit/app/simpleos_nvme_serial_check_spec.spl --mode=interpreter --clean
```

## Do Not Mark Complete Until

- Physical NVMe production run passes on real hardware.
- App-level serial checker passes without native/runtime crash.
- FAT32, NVFS, and DBFS are proven to share the same lease-backed NVMe hardware
  adapter.
- Simple FAT has accepted 4K random read/write evidence against C/VFAT on the
  same-device baseline.
- Legacy FAT code is either removed from production paths by tests or fully
  migrated to shared stdlib code.
