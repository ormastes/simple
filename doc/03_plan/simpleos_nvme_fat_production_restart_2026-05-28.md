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
  interpreter when the default execution mode is JIT. The workspace `bin/simple`
  has been refreshed enough for direct checker invocation to reject missing
  production markers without a native/runtime crash.
- 2026-05-28 same-device contract follow-up: the OS NVMe performance-contract
  line builder now emits the same FAT32/NVFS/DBFS extent-source and VFAT
  same-device baseline markers required by the serial checker, so generated
  production perf lines no longer lag the validation contract.
- 2026-05-28 spoof-resistance follow-up: the serial checker rejects duplicate
  critical `nvme_perf` fields in a single report, so contradictory same-line
  markers such as `qemu=false ... qemu=true` or duplicate VFAT baseline device
  claims cannot be accepted by first-value parsing.

## Known Remaining Work

1. Prove the physical NVMe production lane on real hardware.
   - Run `scripts/run_simpleos_physical_nvme_perf.shs --production --serial-log <path>`.
   - Verify the log with `src/app/simpleos_nvme_serial_check/main.spl`.
   - Required evidence includes `hardware_target=real-nvme`, `qemu=false`,
     `physical_runs>=3`, direct 4K shared-DMA paths, FAT32/NVFS/DBFS consumer
     markers, and same-device C/VFAT comparison fields.
   - Current host preflight is not sufficient for production: all visible
     `/dev/nvme*n1` namespaces report `namespace_nsid=1` only, so the wrapper
     cannot produce the required distinct same-controller user namespace report
     on this host.

2. Keep the serial checker crash fix covered while collecting real production
   evidence.
   - DONE for the production/release lane used by
     `scripts/run_simpleos_physical_nvme_perf.shs`: `test/unit/app/simpleos_nvme_serial_check_spec.spl`
     passes 26 examples in interpreter-driven SPipe.
   - The checker now owns a minimal local serial-evidence gate and the wrapper
     passes serial/preflight/report paths through `SIMPLEOS_NVME_*` environment
     variables under `SIMPLE_EXECUTION_MODE=interpret`.
   - Standalone preflight now enforces the same exactly-one namespace device
     rule as production preflight, preventing ambiguous `/dev/nvme*n1` host
     evidence from reaching identity comparison.
   - Standalone preflight now also validates the same sysfs identity and
     distinct same-controller user namespace topology even when no report path
     is requested; a fake device file without sysfs identity is rejected.
   - The wrapper rejects validation reports that alias the serial log path, so
     live capture cannot overwrite the raw serial evidence after validation.
   - Follow-up source fix: the Rust driver now forces this checker source path
     through the interpreter in JIT mode. Current workspace `bin/simple` direct
     invocation exits 1 with missing physical NVMe marker instead of signal 139.
   - Still open outside this production lane: the default workspace JIT runtime
     still exits 139 for general nil-coalescing/text paths such as
     `"abc".len()` and `nil ?? ""`. Tracked as
     `doc/08_tracking/bug/jit_text_extern_return_segfault_2026-05-28.md`.

## Restart Evidence — 2026-05-28

```text
bin/simple test test/unit/os/services/vfs/vfs_pure_fat_production_guard_spec.spl --mode=interpreter --clean
  PASSED: 2 examples, 0 failures; includes source-tree scan that rejects
  legacy Fat32Driver imports/constructors and legacy FAT helper-module imports
  outside the isolated compatibility module
bin/simple test test/unit/os/services/vfs/nvme_filesystem_mounts_spec.spl --mode=interpreter --clean
  PASSED: 18 examples, 0 failures; confirms NVMe FAT mount factory uses
  FsFat32Driver.new_with_direct_io for lease-backed direct I/O
bin/simple test test/integration/storage/dbfs/dbfs_hw_passthrough_spec.spl --mode=interpreter --clean
  PASSED: 4 examples, 0 failures; confirms DBFS and shared FsFat32Driver
  variants register through the same MountTable driver path
rg -n "Fat32Driver\\.new_ram_backed|impl Fat32Driver:|new_ram_backed" src/os/services/fat32 src/lib/nogc_sync_mut/fs_driver/fat32_stub.spl src/lib/nogc_async_mut/fs_driver/fat32_stub.spl test/integration/storage/dbfs -g '*.spl'
  PASSED: legacy Fat32Driver no longer exposes new_ram_backed/new_ram_backed_with_file shims;
  shared FsFat32Driver constructors remain for current DBFS/shared-driver tests
bin/simple test test/integration/storage/dbfs/fat32_no_regression_spec.spl --mode=interpreter --clean
  PASSED: 3 examples, 0 failures; stale shim-style path traversal assertions
  were replaced with shared FsFat32Driver mount-table registration and DBFS
  coexistence assertions
bin/simple test test/unit/os/services/vfs/vfs_boot_nvme_lease_spec.spl --mode=interpreter --clean
  PASSED: 27 examples, 0 failures
bin/simple test test/unit/os/drivers/nvme/nvme_driver_probe_contract_spec.spl --mode=interpreter --clean
  PASSED: 7 examples, 0 failures
bin/simple test test/unit/os/drivers/nvme/nvme_performance_contract_spec.spl --mode=interpreter --clean
  PASSED: 14 examples, 0 failures
bin/simple test test/unit/app/simpleos_nvme_serial_check_spec.spl --mode=interpreter --clean
  PASSED: 26 examples, 0 failures
bin/simple check src/os/drivers/nvme/nvme_performance_contract.spl test/unit/os/drivers/nvme/nvme_performance_contract_spec.spl
  PASSED: exit code 0
bin/simple test test/unit/os/drivers/real_device_readiness_spec.spl --mode=interpreter --clean
  PASSED: 8 examples, 0 failures
SIMPLE_EXECUTION_MODE=interpret SIMPLEOS_NVME_SERIAL_LOG=/tmp/nonexistent-simpleos-nvme.log bin/simple run src/app/simpleos_nvme_serial_check/main.spl
  PASSED: no crash, exits 1 with missing-marker rejection
SIMPLEOS_NVME_SERIAL_LOG=/tmp/nonexistent-simpleos-nvme.log bin/simple run src/app/simpleos_nvme_serial_check/main.spl
  PASSED: no crash, exits 1 with missing physical NVMe marker
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
scripts/perf/run-fat32-4k-cfat-baseline.shs
  FAILED after clean full-cluster overwrite optimization: Simple FAT32 read
  p50/p99 13us/21us, write p50/p99 39us/42us; direct C FAT32 read p50/p99
  32us/76us, write p50/p99 26us/46us; VFAT skipped because the existing
  /tmp/simple_vfat_bench_mnt mount is unseeded/not writable by this user
scripts/perf/run-fat32-4k-cfat-baseline.shs
  PASSED latest isolated direct C comparison: Simple FAT32 read p50/p99 12us/19us,
  write p50/p99 34us/37us; direct C FAT32 read p50/p99 40us/71us, write
  p50/p99 45us/84us; VFAT still skipped because the local mount is unseeded
  or not writable by this user
REQUIRE_VFAT_BASELINE=1 scripts/perf/run-fat32-4k-cfat-baseline.shs
  FAILED cleanly: VFAT baseline is required but missing or unseeded; no shell
  integer-expression error from SKIPPED rows after parser tightening
REQUIRE_VFAT_BASELINE=1 VFAT_MNT=/tmp/simple_vfat_bench_mnt_codex scripts/perf/run-fat32-4k-cfat-baseline.shs
  FAILED cleanly: custom VFAT mount path is propagated into a generated
  benchmark source copy, and missing/unseeded VFAT rows fail before integer
  comparison rather than parsing SKIPPED as a number
scripts/perf/prepare-fat32-4k-vfat.shs
  FAILED locally: /tmp/simple_vfat_bench_mnt is mounted rw as /dev/loop21 but
  owned by root:root, and passwordless sudo is unavailable for remount/reseed;
  the script now has a udisksctl fallback for a free mount point, but this
  stale root-owned mount must still be removed or remounted before the focused
  benchmark can consume VFAT files at its fixed path
VFAT_MNT=/tmp/simple_vfat_bench_mnt_codex scripts/perf/prepare-fat32-4k-vfat.shs
  FAILED locally: no passwordless sudo and udisksctl loop setup is denied by
  polkit without a controlling terminal; this proves the repo gate can use a
  non-default mount path, but local VFAT seeding still requires external mount
  authorization
sh scripts/run_simpleos_physical_nvme_perf.shs --preflight --report-out /tmp/simpleos_nvme_preflight_probe.sdn
  FAILED locally: default /dev/nvme*n1 matched 3 real NVMe namespaces, and
  standalone preflight now fails closed before identity probing when the device
  glob is ambiguous
SIMPLEOS_NVME_DEVICE_GLOB=/dev/nvme{0,1,2}n1 sh scripts/run_simpleos_physical_nvme_perf.shs --preflight --report-out /tmp/simpleos_<dev>_preflight.sdn
  FAILED for each visible namespace: nvme0n1, nvme1n1, and nvme2n1 all report
  namespace_nsid=1 only, with no distinct user namespace on the same controller
bin/simple check test/unit/app/simpleos_nvme_serial_check_spec.spl src/app/simpleos_nvme_serial_check/main.spl
  PASSED: exit code 0
bin/simple check src/app/simpleos_nvme_serial_check/main.spl test/unit/app/simpleos_nvme_serial_check_spec.spl
  PASSED: exit code 0
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
   - DONE for production-path enforcement: `vfs_pure_fat_production_guard_spec`
     now walks `src/os` and rejects legacy FAT imports/constructors outside the
     isolated compatibility module files. Latest follow-up also rejects legacy
     FAT helper-module imports (`fat32_write`, `fat32_filesystem_ops`,
     `fat32_write_helpers`) outside that compatibility island.
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
   - 2026-05-28 follow-up: removed unused `Fat32Driver.new_ram_backed*`
     compatibility constructors from the legacy implementation island. Current
     DBFS/shared-driver coverage uses `FsFat32Driver.new_ram_backed*` directly;
     `test/integration/storage/dbfs/dbfs_hw_passthrough_spec.spl` passes.
   - 2026-05-28 follow-up:
     `test/integration/storage/dbfs/fat32_no_regression_spec.spl` no longer
     asserts obsolete shim-style FAT path traversal against an unmounted mock
     image. It now passes as a focused shared `FsFat32Driver` mount-table
     registration and DBFS coexistence guard, and its path-migration conflict
     has been resolved toward the shared-driver surface.

4. Finish performance proof for Simple FAT vs C/VFAT on 4K random read/write.
   - Keep `scripts/perf/run-fat32-4k-cfat-baseline.shs` as the focused gate.
   - Require VFAT baseline when making the stronger “faster than C FAT” claim.
   - Record median/p50/p99 evidence, not single-sample claims.
   - 2026-05-28 follow-up: full aligned 4K FAT overwrites now use a clean
     cluster write path that avoids dirty-cache bookkeeping, improving Simple
     FAT32 write p99 from 41us to 37us in the host gate, but the focused gate
     remained noisy across local runs.
   - 2026-05-28 latest rerun: the focused direct C comparison now passes with
     Simple FAT32 read/write p50 13us/34us versus direct C FAT32 read/write
     p50 38us/46us.
     Tracked in
     `doc/08_tracking/bug/fat32_4k_overwrite_c_baseline_gap_2026-05-28.md`.
   - 2026-05-28 VFAT follow-up: the preparation script exists, but the local
     mount is root-owned and cannot be reseeded without passwordless sudo or a
     remount with `uid=$(id -u),gid=$(id -g)`. The script now also attempts a
     `udisksctl` loop mount when the target mount point is free.
   - 2026-05-28 VFAT path follow-up: `run-fat32-4k-cfat-baseline.shs` now
     honors `VFAT_MNT` by generating a temporary benchmark source with that
     mount path as a literal, avoiding the Simple runtime crashes seen when
     trying to read the path via argv/env inside the benchmark.

5. Audit direct I/O for all three filesystem consumers.
   - FAT32 is wired through shared FAT extents.
   - NVFS/DBFS direct I/O markers exist, but real hardware proof must show the
     same NVMe adapter and lease-backed queue path for all consumers.
   - DONE for serial-contract alignment: `nvme_production_perf_report_line`
     now emits `fat32_extent_source`, `nvfs_extent_source`,
     `dbfs_extent_source`, and same-device VFAT baseline markers, and the
     parser rejects spoofed VFAT baseline devices.

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
- App-level serial checker verifies a real production serial log without
  native/runtime crash.
- FAT32, NVFS, and DBFS are proven to share the same lease-backed NVMe hardware
  adapter.
- Simple FAT has accepted 4K random read/write evidence against C/VFAT on the
  same-device baseline.
- Legacy FAT code is either removed from production paths by tests or fully
  migrated to shared stdlib code.
