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
- 2026-05-28 local restart evidence: the production/release serial checker
  lane now passes the app-level SPipe spec and validates preflight identity,
  FAT32/NVFS/DBFS direct-I/O markers, same-device C baseline markers, and
  duplicate perf report rejection without the prior `file_modified_time`
  app-spec failure.
- 2026-05-28 follow-up: the physical NVMe wrapper now invokes the checker with
  `SIMPLE_EXECUTION_MODE=interpret` and environment-provided paths to avoid the
  default JIT text-return extern crash while preserving production validation.
- 2026-05-28 same-device follow-up: preflight reports now record controller,
  user-namespace controller, `user_namespace_same_controller: true`, and
  `same_physical_device: true`; the serial checker rejects supplied preflight
  evidence that omits or contradicts those markers before accepting production
  same-device claims.
- 2026-05-28 follow-up: `ExecCore::run_file_with_args` now forces the
  `src/app/simpleos_nvme_serial_check/main.spl` source path through the
  interpreter when the default execution mode is JIT. The broader nil/text JIT
  crash remains tracked separately, but direct checker invocation no longer
  depends on callers remembering the environment override once the driver is
  rebuilt.

## Known Remaining Work

1. Prove the physical NVMe production lane on real hardware.
   - Run `scripts/run_simpleos_physical_nvme_perf.shs --production --serial-log <path>`.
   - Verify the log with `src/app/simpleos_nvme_serial_check/main.spl`.
   - Required evidence includes `hardware_target=real-nvme`, `qemu=false`,
     `physical_runs>=3`, direct 4K shared-DMA paths, FAT32/NVFS/DBFS consumer
     markers, and same-device C/VFAT comparison fields.

2. Fix the serial checker runtime crash before treating app-level evidence as
   production-grade.
   - DONE for the production/release lane used by
     `scripts/run_simpleos_physical_nvme_perf.shs`: `test/unit/app/simpleos_nvme_serial_check_spec.spl`
     passes 22 examples in interpreter-driven SPipe.
   - The checker now owns a minimal local serial-evidence gate and the wrapper
     passes serial/preflight/report paths through `SIMPLEOS_NVME_*` environment
     variables under `SIMPLE_EXECUTION_MODE=interpret`.
   - Follow-up source fix: the Rust driver now forces this checker source path
     through the interpreter in JIT mode. This needs a rebuilt `bin/simple`
     before the currently installed workspace binary shows the new behavior.
   - Still open outside this production lane: the default workspace JIT runtime
     still exits 139 for general nil-coalescing/text paths such as
     `"abc".len()` and `nil ?? ""`. Tracked as
     `doc/08_tracking/bug/jit_text_extern_return_segfault_2026-05-28.md`.

## Restart Evidence — 2026-05-28

```text
bin/simple test test/unit/os/services/vfs/vfs_pure_fat_production_guard_spec.spl --mode=interpreter --clean
  PASSED: 1 examples, 0 failures
bin/simple test test/unit/os/services/vfs/vfs_boot_nvme_lease_spec.spl --mode=interpreter --clean
  PASSED: 27 examples, 0 failures
bin/simple test test/unit/os/drivers/nvme/nvme_driver_probe_contract_spec.spl --mode=interpreter --clean
  PASSED: 7 examples, 0 failures
bin/simple test test/unit/os/drivers/nvme/nvme_performance_contract_spec.spl --mode=interpreter --clean
  PASSED: 14 examples, 0 failures
bin/simple test test/unit/app/simpleos_nvme_serial_check_spec.spl --mode=interpreter --clean
  PASSED: 22 examples, 0 failures
SIMPLE_EXECUTION_MODE=interpret SIMPLEOS_NVME_SERIAL_LOG=/tmp/nonexistent-simpleos-nvme.log bin/simple run src/app/simpleos_nvme_serial_check/main.spl
  PASSED: no crash, exits 1 with missing-marker rejection
bin/simple test test/unit/lib/fs_driver/fs_hardening_spec.spl --mode=interpreter --clean
  PASSED: 15 examples, 0 failures
bin/simple test test/system/storage_fat32_statfs_truncate_spec.spl --mode=interpreter --clean
  PASSED: 2 examples, 0 failures
bin/simple test test/system/storage_fat32_positional_cursor_spec.spl --mode=interpreter --clean
  PASSED: 2 examples, 0 failures
bin/simple test test/unit/os/port/host_fat32_tree_populator_spec.spl --mode=interpreter --clean
  PASSED: 1 file, 1 example, 0 failures
bin/simple check src/lib/nogc_async_mut/fs_driver/fat32_core.spl src/lib/nogc_sync_mut/fs_driver/fat32_core.spl src/os/port/host_fat32_tree_populator.spl src/os/services/fat32/shared_fat32_driver.spl
  PASSED: exit code 0
bin/simple check src/lib
  PASSED: exit code 0, warnings only
CARGO_TARGET_DIR=target_codex_text_eq cargo build -p simple-driver --bin simple
  PASSED: dev build from fixed Rust sources
src/compiler_rust/target_codex_text_eq/debug/simple run src/app/simpleos_nvme_serial_check/main.spl
  PASSED: no signal; prints usage and exits 2 when SIMPLEOS_NVME_SERIAL_LOG is unset
SIMPLEOS_NVME_SERIAL_LOG=/tmp/nonexistent-simpleos-nvme.log src/compiler_rust/target_codex_text_eq/debug/simple run src/app/simpleos_nvme_serial_check/main.spl
  PASSED: no signal; exits 1 with missing physical NVMe marker
```

3. Retire duplicate legacy FAT implementation safely.
   - Keep production guard in place.
   - DONE: hardening helpers (`Fat32Bpb`, `validate_bpb`,
     `detect_cluster_cycle`) now live in shared stdlib FAT modules
     (`std.fs_driver.fat32_hardening` in sync/async runtimes), and
     `test/unit/lib/fs_driver/fs_hardening_spec.spl` imports the shared
     surface.
   - DONE: host FAT image populator now uses shared
     `std.fs_driver.fat32_core.Fat32Core`, not legacy
     `os.services.fat32.fat32.Fat32Driver`. Its image adapter reads/writes the
     backing image file on sector operations so the shared core sees committed
     nested-directory state in the interpreter/runtime trait path.
   - DONE: system FAT32 statfs/truncate and positional-cursor specs now target
     shared `std.fs_driver.fat32_core` instead of directly instantiating the
     legacy `Fat32Driver`.
   - DONE for debug coverage: `_debug_host_fat32_tree_populator.spl` now uses
     the shared `Fat32Core` image-population path for manual sector dumps.
   - 2026-05-28 follow-up: the debug helper now exits 0 with
     `Result::Ok(())` after removing a local `io` alias lowering blocker from
     the cached raw-image device and replacing JIT-incompatible `Result.Ok`
     returns on that path. JIT still falls back on a broader wildcard-pattern
     lowering limitation in the loaded library set, but the interpreter debug
     evidence is usable.
   - Still open: the legacy FAT module's own internal tests still instantiate
     `Fat32Driver` until the legacy module is deleted or converted into a
     compatibility wrapper.
   - Existing legacy-driver blocker: `test/unit/os/services/fat32/fat32_spec.spl`
     reports 19 passed / 8 failed in this worktree and in a detached clean
     `HEAD` worktree. Keep that as pre-existing legacy FAT debt while retiring
     production dependencies on the old driver.

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
bin/simple test test/unit/lib/fs_driver/fs_hardening_spec.spl --mode=interpreter --clean
bin/simple test test/system/storage_fat32_statfs_truncate_spec.spl --mode=interpreter --clean
bin/simple test test/system/storage_fat32_positional_cursor_spec.spl --mode=interpreter --clean
bin/simple test test/unit/os/port/host_fat32_tree_populator_spec.spl --mode=interpreter --clean
bin/simple check src/lib
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
