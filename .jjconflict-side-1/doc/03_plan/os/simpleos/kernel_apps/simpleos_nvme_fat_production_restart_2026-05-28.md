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
- 2026-05-28 contract spoof-resistance follow-up: the lower-level NVMe
  performance contract now rejects duplicate same-line evidence fields before
  any first-value parsing, and the app checker also rejects duplicate
  user-namespace evidence fields such as `user_namespace_nsid=`.
- 2026-05-28 preflight spoof-resistance follow-up: supplied host preflight
  reports now reject duplicate identity fields such as `serial:` before
  comparing serial evidence, so contradictory preflight reports cannot pass by
  first-value parsing.
- 2026-05-28 VFAT gate follow-up: `REQUIRE_VFAT_BASELINE=1` now checks the
  configured VFAT mount and seed files before compiling/running the repeated
  Simple/C benchmark, so missing same-device VFAT setup fails immediately with
  the exact mount path.
- 2026-05-28 VFAT filesystem follow-up: the VFAT-required gate and preparation
  script now reject seeded files on non-VFAT filesystems, preventing a plain
  tmpfs/ext4 directory from satisfying the same-device VFAT baseline.
- 2026-05-28 VFAT preparation follow-up: the VFAT preparation helper now
  validates `VFAT_SIZE_MIB` as a positive integer before creating the mount
  path or image file, so invalid image sizing fails before any privileged
  mount/setup side effects.
- 2026-05-28 VFAT benchmark path follow-up: the repeated benchmark runner now
  rejects non-absolute, control-character, or filesystem-root `VFAT_MNT`
  values before generating the temporary benchmark source used for custom mount
  paths.
- 2026-05-29 VFAT evidence follow-up: required VFAT mode now removes stale
  `build/os/perf/VFAT4K.TXT` and the generated custom-mount benchmark source
  before input validation and readiness checks, so invalid or not-ready
  required baseline runs cannot leave old ready/custom artifacts behind.
- 2026-05-28 VFAT preparation path follow-up: the preparation helper now
  applies the same absolute/no-control-character `VFAT_MNT` gate before
  creating the mount directory.
- 2026-05-28 VFAT image path follow-up: the preparation helper now rejects
  non-absolute or control-character `VFAT_IMG` values before creating the mount
  directory or image artifact.
- 2026-05-28 VFAT image alias follow-up: the preparation helper now rejects
  `VFAT_IMG` values that equal `VFAT_MNT` before creating or removing either
  path.
- 2026-05-28 VFAT image containment follow-up: the preparation helper now
  rejects `VFAT_IMG` values inside `VFAT_MNT` before creating the mount
  directory, preventing the backing image from being placed under the mount
  target.
- 2026-05-28 VFAT root path follow-up: the preparation helper now rejects
  filesystem root as `VFAT_MNT` or `VFAT_IMG` before diagnosis or setup can
  treat `/` as a benchmark mount target or backing image path.
- 2026-05-28 VFAT image parent follow-up: the preparation helper now requires
  the `VFAT_IMG` parent directory to exist and be writable before diagnosis or
  setup creates the mount directory.
- 2026-05-28 VFAT readiness follow-up: the preparation helper now supports
  `--diagnose`, which validates inputs and reports mount/tool/seed readiness
  without creating the mount directory, image, or seed files. This gives
  rootless hosts explicit evidence for why the same-device VFAT baseline cannot
  be prepared locally, while preserving the production requirement that actual
  benchmark seeds live on a writable `vfat`/`msdos` mount.
- 2026-05-28 physical preflight scan follow-up: the physical NVMe wrapper now
  has `--preflight-scan` to test each matched namespace independently and emit
  per-device readiness/failure reasons before an operator chooses the
  production `SIMPLEOS_NVME_DEVICE_GLOB`. The scan exits nonzero when zero or
  multiple namespaces are ready, so production capture must be pinned to one
  unambiguous namespace. With `--report-out`, it writes a durable scan report
  for zero-match scans and for scans with candidates, records every candidate
  when present, embeds the generated preflight identity for ready candidates,
  and records the final ready/not-ready/ambiguous summary.
  With `--preflight-out`, an unambiguous scan also writes the selected
  production preflight report and ambiguous/not-ready scans leave no selected
  preflight output. `--preflight-out` now requires `--report-out` so selected
  preflight evidence is always tied to the durable scan report. Stale selected
  preflight output is removed at scan startup, and ready scan summaries name
  the selected preflight report path. Scan temporary files are trap-cleaned on
  early exits and normal not-ready/ambiguous paths.
- 2026-05-28 live-capture atomicity follow-up: one-shot
  `--production --preflight-out` now stages generated preflight identity in a
  temporary file and promotes it only after serial capture has produced a
  non-empty serial log. A missing serial port leaves no selected preflight,
  validation report, serial log, or temporary preflight residue.
- 2026-05-29 legacy FAT retirement follow-up: shared `Fat32Core` now consumes
  single-slot FAT32 LFN entries when reading directories and resolves them
  case-insensitively through the shared core path. This moves another legacy
  `Fat32Driver`-only behavior into the production/shared FAT implementation.

## Known Remaining Work

1. Prove the physical NVMe production lane on real hardware.
   - Run `scripts/os/run_simpleos_physical_nvme_perf.shs --production --serial-log <path>`.
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
     `scripts/os/run_simpleos_physical_nvme_perf.shs`: `test/01_unit/app/simpleos_nvme_serial_check_spec.spl`
     passes 32 examples in interpreter-driven SPipe when the wrapper is pointed
     at the current debug CLI with `SIMPLEOS_SIMPLE_BIN=src/compiler_rust/target/debug/simple`.
   - The checker now owns a minimal local serial-evidence gate and the wrapper
     passes serial/preflight/report paths through `SIMPLEOS_NVME_*` environment
     variables under `SIMPLE_EXECUTION_MODE=interpret`.
   - Standalone preflight now enforces the same exactly-one namespace device
     rule as production preflight, preventing ambiguous `/dev/nvme*n1` host
     evidence from reaching identity comparison.
   - The wrapper now also supports `--preflight-scan` to evaluate every matched
     namespace separately and report exactly which device, if any, has the
     required distinct same-controller user namespace. The scan rejects both
     zero-ready and multiple-ready results.
   - Standalone preflight now also validates the same sysfs identity and
     distinct same-controller user namespace topology even when no report path
     is requested; a fake device file without sysfs identity is rejected.
   - The wrapper rejects validation reports that alias the serial log path, so
     live capture cannot overwrite the raw serial evidence after validation.
   - Live one-shot production capture now avoids stale selected-preflight
     evidence by promoting `--preflight-out` only after serial capture creates
     a non-empty log.
   - Follow-up source fix: the Rust driver now forces this checker source path
     through the interpreter in JIT mode. Current workspace `bin/simple` direct
     invocation exits 1 with missing physical NVMe marker instead of signal 139.
   - Still open outside this production lane: the default workspace JIT runtime
     still exits 139 for general nil-coalescing/text paths such as
     `"abc".len()` and `nil ?? ""`. Tracked as
     `doc/08_tracking/bug/jit_text_extern_return_segfault_2026-05-28.md`.

## Restart Evidence — 2026-05-28

```text
bin/simple test test/01_unit/os/services/vfs/vfs_pure_fat_production_guard_spec.spl --mode=interpreter --clean
  PASSED: 2 examples, 0 failures; includes source-tree scan that rejects
  legacy Fat32Driver imports/constructors and legacy FAT helper-module imports
  outside the isolated compatibility module
bin/simple check src/os/services/fat32/fat32.spl src/os/services/fat32/fat32_write.spl test/01_unit/os/services/fat32/fat32_spec.spl
  PASSED: exit code 0; isolated legacy FAT implementation now uses the current
  std BlockDevice read_sector(lba) return-buffer shape for cluster reads
bin/simple test test/01_unit/os/services/fat32/fat32_spec.spl --mode=interpreter --clean
  PASSED: 27 examples, 0 failures after removing stale buffer-style
  read_sector calls, updating BPB constructor coverage to the current compact
  legacy BPB shape, avoiding nested optional unwraps in the spec, and assigning
  mutated BPB sector bytes back into the mock device
bin/simple test test/01_unit/os/services/vfs/nvme_filesystem_mounts_spec.spl --mode=interpreter --clean
  PASSED: 18 examples, 0 failures; confirms NVMe FAT mount factory uses
  FsFat32Driver.new_with_direct_io for lease-backed direct I/O
bin/simple test test/02_integration/storage/dbfs/dbfs_hw_passthrough_spec.spl --mode=interpreter --clean
  PASSED: 4 examples, 0 failures; confirms DBFS and shared FsFat32Driver
  variants register through the same MountTable driver path
rg -n "Fat32Driver\\.new_ram_backed|impl Fat32Driver:|new_ram_backed" src/os/services/fat32 src/lib/nogc_sync_mut/fs_driver/fat32_stub.spl src/lib/nogc_async_mut/fs_driver/fat32_stub.spl test/02_integration/storage/dbfs -g '*.spl'
  PASSED: legacy Fat32Driver no longer exposes new_ram_backed/new_ram_backed_with_file shims;
  shared FsFat32Driver constructors remain for current DBFS/shared-driver tests
bin/simple test test/02_integration/storage/dbfs/fat32_no_regression_spec.spl --mode=interpreter --clean
  PASSED: 3 examples, 0 failures; stale shim-style path traversal assertions
  were replaced with shared FsFat32Driver mount-table registration and DBFS
  coexistence assertions
bin/simple test test/01_unit/os/services/vfs/vfs_boot_nvme_lease_spec.spl --mode=interpreter --clean
  PASSED: 27 examples, 0 failures
bin/simple test test/01_unit/os/drivers/nvme/nvme_driver_probe_contract_spec.spl --mode=interpreter --clean
  PASSED: 7 examples, 0 failures
bin/simple test test/01_unit/os/drivers/nvme/nvme_performance_contract_spec.spl --mode=interpreter --clean
  PASSED: 14 examples, 0 failures
bin/simple test test/01_unit/app/simpleos_nvme_serial_check_spec.spl --mode=interpreter --clean
  PASSED: 31 examples, 0 failures; includes duplicate critical-field rejection
  for `qemu=`, `vfat_baseline_device=`, user-namespace evidence fields, and
  supplied preflight identity fields such as `serial:`; also covers
  `--preflight-scan` selecting the single namespace with a distinct
  same-controller user namespace from fake sysfs candidates and rejecting
  multiple-ready ambiguous scans; scan cases also verify durable
  `--report-out` summaries for ready, ambiguous, and not-ready scans, embed
  ready-candidate preflight identity, write a selected `--preflight-out` only
  for unambiguous ready scans, and fail closed instead of overwriting an
  existing scan report or aliasing scan/preflight output paths. The not-ready
  scan case also verifies selected preflight temporary files are removed.
src/compiler_rust/target/debug/simple test test/01_unit/os/drivers/nvme/nvme_physical_preflight_script_spec.spl --mode=interpreter --clean
  PASSED: 8 examples, 0 failures; wrapper-only coverage for
  `--preflight-scan` writing both durable scan and selected preflight reports
  for one ready namespace, linking the selected preflight path from the scan
  summary, requiring `--report-out` before `--preflight-out`, rejecting
  scan/preflight output path aliasing, refusing to overwrite an existing scan
  report, replacing stale selected preflight output for ready scans, removing
  selected preflight temp output for not-ready scans with and without matched
  namespace devices, and
  suppressing selected preflight output plus `selected_preflight_report`
  summary fields for ambiguous scans without invoking the app checker runtime.
bin/simple check src/os/drivers/nvme/nvme_performance_contract.spl test/01_unit/os/drivers/nvme/nvme_performance_contract_spec.spl
  PASSED: exit code 0
bin/simple test test/01_unit/os/drivers/nvme/nvme_performance_contract_spec.spl --mode=interpreter --clean
  PASSED: 14 examples, 0 failures; lower-level production and real-hardware
  perf parsers reject duplicate same-line fields such as `qemu=` and
  `vfat_baseline_device=` instead of accepting first-value spoofing
bin/simple test test/01_unit/os/drivers/real_device_readiness_spec.spl --mode=interpreter --clean
  PASSED: 8 examples, 0 failures
SIMPLE_EXECUTION_MODE=interpret SIMPLEOS_NVME_SERIAL_LOG=/tmp/nonexistent-simpleos-nvme.log bin/simple run src/app/simpleos_nvme_serial_check/main.spl
  PASSED: no crash, exits 1 with missing-marker rejection
SIMPLEOS_NVME_SERIAL_LOG=/tmp/nonexistent-simpleos-nvme.log bin/simple run src/app/simpleos_nvme_serial_check/main.spl
  PASSED: no crash, exits 1 with missing physical NVMe marker
bin/simple test test/01_unit/lib/fs_driver/fs_hardening_spec.spl --mode=interpreter --clean
  PASSED: 15 examples, 0 failures
bin/simple test test/03_system/storage_fat32_statfs_truncate_spec.spl --mode=interpreter --clean
  PASSED: 2 examples, 0 failures
bin/simple test test/03_system/storage_fat32_positional_cursor_spec.spl --mode=interpreter --clean
  PASSED: 2 examples, 0 failures
bin/simple test test/01_unit/os/port/host_fat32_tree_populator_spec.spl --mode=interpreter --clean
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
2026-05-28 current re-probe:
  findmnt shows no active VFAT mount at /tmp/simple_vfat_bench_mnt or
  /tmp/simple_vfat_bench_mnt_codex, and
  VFAT_MNT=/tmp/simple_vfat_bench_mnt_codex scripts/perf/prepare-fat32-4k-vfat.shs
  still fails because sudo is unavailable and udisksctl loop setup is denied by
  polkit without a controlling terminal.
FAT32_4K_RUNS=1 REQUIRE_VFAT_BASELINE=1 VFAT_MNT=/tmp/simple_vfat_bench_mnt_codex scripts/perf/run-fat32-4k-cfat-baseline.shs
  FAILED cleanly after median-summary output because VFAT baseline rows remain
  missing or unseeded at the configured mount path.
FAT32_4K_RUNS=1 REQUIRE_VFAT_BASELINE=1 VFAT_MNT=/tmp/simple_vfat_bench_mnt_codex scripts/perf/run-fat32-4k-cfat-baseline.shs
  PASSED gate behavior follow-up: now fails immediately before compiling or
  running benchmarks with `VFAT baseline is required but missing or unseeded at
  /tmp/simple_vfat_bench_mnt_codex`
FAT32_4K_RUNS=1 REQUIRE_VFAT_BASELINE=1 VFAT_MNT=/dev/shm scripts/perf/run-fat32-4k-cfat-baseline.shs
  PASSED gate behavior follow-up: seeded files on writable tmpfs are rejected
  because the configured baseline path is not vfat/msdos.
VFAT_MNT=/dev/shm scripts/perf/prepare-fat32-4k-vfat.shs
  PASSED gate behavior follow-up: existing writable non-VFAT mount is rejected
  with `VFAT baseline mount is not vfat/msdos: /dev/shm (fstype=tmpfs)`.
bin/simple test test/01_unit/os/drivers/nvme/nvme_vfat_baseline_script_spec.spl --mode=interpreter --clean
  PASSED: 16 examples, 0 failures; covers non-mutating VFAT preparation
  diagnosis, non-positive FAT32_4K_RUNS rejection, non-positive VFAT_SIZE_MIB
  rejection before mount path creation, relative VFAT_MNT rejection before
  temporary benchmark source generation, filesystem-root VFAT_MNT rejection
  before temporary benchmark source generation, relative VFAT_MNT rejection
  before preparation mount directory creation, filesystem-root VFAT_MNT
  rejection before diagnosis/setup artifacts, filesystem-root VFAT_IMG
  rejection before diagnosis/setup artifacts, missing VFAT_IMG parent
  rejection before preparation artifacts are created, unwritable VFAT_IMG
  parent rejection before preparation artifacts are created, relative VFAT_IMG
  rejection before preparation artifacts are created, VFAT_IMG/VFAT_MNT alias
  rejection before either path is created, VFAT_IMG-inside-VFAT_MNT rejection
  before mount directory creation, required VFAT rejection when seed files live
  on a non-VFAT filesystem, stale VFAT4K evidence removal before required-mode
  input validation and not-ready failures, stale custom benchmark source
  removal before required-mode input validation failures, and prepare-script
  rejection of an existing writable non-VFAT mount.
FAT32_4K_RUNS=0 scripts/perf/run-fat32-4k-cfat-baseline.shs
  FAILED cleanly with a positive-integer validation error for the repeated-run
  count knob.
sh scripts/os/run_simpleos_physical_nvme_perf.shs --preflight --report-out /tmp/simpleos_nvme_preflight_probe.sdn
  FAILED locally: default /dev/nvme*n1 matched 3 real NVMe namespaces, and
  standalone preflight now fails closed before identity probing when the device
  glob is ambiguous
SIMPLEOS_NVME_DEVICE_GLOB=/dev/nvme{0,1,2}n1 sh scripts/os/run_simpleos_physical_nvme_perf.shs --preflight --report-out /tmp/simpleos_<dev>_preflight.sdn
  FAILED for each visible namespace: nvme0n1, nvme1n1, and nvme2n1 all report
  namespace_nsid=1 only, with no distinct user namespace on the same controller
2026-05-28 current re-probe:
  sh scripts/os/run_simpleos_physical_nvme_perf.shs --preflight --report-out /tmp/simpleos_nvme_preflight_probe_current.sdn
  still fails because /dev/nvme*n1 matches three namespace devices.
  Explicit per-device preflight for /dev/nvme0n1, /dev/nvme1n1, and
  /dev/nvme2n1 still fails with no distinct assignable user namespace.
sh scripts/os/run_simpleos_physical_nvme_perf.shs --preflight-scan --report-out /tmp/simpleos_nvme_preflight_scan_current.sdn --preflight-out /tmp/simpleos_nvme_preflight_current.sdn
  FAILED locally after testing all default matches independently:
  /dev/nvme0n1, /dev/nvme1n1, and /dev/nvme2n1 each report no distinct
  assignable user namespace, producing `preflight-scan=not-ready
  matched_devices=3 ready_devices=0`; the report file records
  `accepted: false`, `status: not-ready`, `matched_devices: 3`, and
  `ready_devices: 0`, and no selected preflight report is created.
Manual fake-sysfs scan cleanup check
  PASSED: not-ready scan with both `--report-out` and `--preflight-out`
  writes the rejected scan report, leaves no selected preflight output, and
  leaves no selected preflight temp file.
src/compiler_rust/target/debug/simple check src/app/simpleos_nvme_serial_check/main.spl test/01_unit/app/simpleos_nvme_serial_check_spec.spl
  PASSED: exit code 0
SIMPLEOS_SIMPLE_BIN=src/compiler_rust/target/debug/simple SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/01_unit/app/simpleos_nvme_serial_check_spec.spl --mode=interpreter --clean --format json
  PASSED: 32 examples, 0 failures; includes the live-capture atomicity guard
  for `--production --preflight-out`.
CARGO_TARGET_DIR=target_codex_text_eq cargo build -p simple-driver --bin simple
  PASSED: dev build from fixed Rust sources
src/compiler_rust/target_codex_text_eq/debug/simple run src/app/simpleos_nvme_serial_check/main.spl
  PASSED: no signal; prints usage and exits 2 when SIMPLEOS_NVME_SERIAL_LOG is unset
SIMPLEOS_NVME_SERIAL_LOG=/tmp/nonexistent-simpleos-nvme.log src/compiler_rust/target_codex_text_eq/debug/simple run src/app/simpleos_nvme_serial_check/main.spl
  PASSED: no signal; exits 1 with missing physical NVMe marker
Manual fake-sysfs live-capture atomicity check
  PASSED: `--production --preflight-out` with a valid fake same-controller
  namespace pair and SERIAL_PORT=/tmp/simpleos_nvme_missing_serial_port exits
  2 with `serial port not found`, leaves no selected preflight report, no
  selected preflight temp file, no validation report, and no serial log.
Manual fake-sysfs one-shot preflight checks
  PASSED: incomplete sysfs identity exits 1 with `incomplete NVMe sysfs
  identity` before serial capture; two fake namespace matches exit 1 with
  `production preflight requires exactly one NVMe namespace device; matched 2`
  before serial capture.
```

3. Retire duplicate legacy FAT implementation safely.
   - Keep production guard in place.
   - DONE: hardening helpers (`Fat32Bpb`, `validate_bpb`,
     `detect_cluster_cycle`) now live in shared stdlib FAT modules
     (`std.fs_driver.fat32_hardening` in sync/async runtimes), and
     `test/01_unit/lib/fs_driver/fs_hardening_spec.spl` imports the shared
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
   - 2026-05-28 legacy spec follow-up:
     `test/01_unit/os/services/fat32/fat32_spec.spl` now passes 27 examples.
     The isolated legacy implementation was updated away from stale
     buffer-style `read_sector(lba, buf)` calls, and the spec was aligned with
     the compact legacy BPB struct plus current optional-unwrapping behavior.
     This does not re-admit legacy FAT into production paths; the production
     guard remains the release-blocking evidence for that boundary.
   - 2026-05-28 follow-up: removed unused `Fat32Driver.new_ram_backed*`
     compatibility constructors from the legacy implementation island. Current
     DBFS/shared-driver coverage uses `FsFat32Driver.new_ram_backed*` directly;
     `test/02_integration/storage/dbfs/dbfs_hw_passthrough_spec.spl` passes.
   - 2026-05-28 follow-up:
     `test/02_integration/storage/dbfs/fat32_no_regression_spec.spl` no longer
     asserts obsolete shim-style FAT path traversal against an unmounted mock
     image. It now passes as a focused shared `FsFat32Driver` mount-table
     registration and DBFS coexistence guard, and its path-migration conflict
     has been resolved toward the shared-driver surface.
   - 2026-05-29 follow-up: shared `Fat32Core` now parses single-slot LFN
     directory entries and resolves them case-insensitively, with
     `test/01_unit/lib/fs_driver/fat32_core_lfn_spec.spl` covering the shared
     behavior that used to be exercised only through the legacy driver.

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
   - 2026-05-28 current re-probe: the focused direct C gate remains noisy. One
     run failed with Simple write p50 44us versus direct C write p50 34us; the
     immediate rerun passed with Simple write p50 38us versus direct C write
     p50 45us. Treat single-run direct-C success as weak evidence until VFAT is
     mounted and repeated same-device runs are collected.
   - 2026-05-28 repeated-run gate follow-up:
     `scripts/perf/run-fat32-4k-cfat-baseline.shs` now defaults to
     `FAT32_4K_RUNS=3` and compares median p50 across runs. The first median
     run passed direct C with Simple read/write median p50 13us/34us versus
     direct C read/write median p50 37us/43us. VFAT is still required for the
     stronger same-device baseline claim.
   - 2026-05-28 latest repeated run: direct-C median p50 still passes with
     Simple read/write 13us/34us versus direct C read/write 39us/47us; VFAT was
     skipped because no writable seeded same-device VFAT mount is present.
   - 2026-05-28 VFAT-required gate follow-up: required VFAT mode now validates
     seed-file presence and writability before benchmark compilation, so a
     missing mount fails fast at the configured `VFAT_MNT` path.
   - 2026-05-28 VFAT filesystem follow-up: required VFAT mode and the
     preparation helper now require `findmnt` to report `vfat` or `msdos` for
     the configured path, so a seeded tmpfs/ext4 directory cannot spoof the
     Linux VFAT baseline.
   - 2026-05-28 VFAT preparation follow-up: the preparation helper validates
     `VFAT_SIZE_MIB` before creating the mount path or image, preventing
     invalid sizing from reaching `dd`/mount setup.
   - 2026-05-28 VFAT benchmark path follow-up: the repeated benchmark runner
     rejects non-absolute, control-character, or filesystem-root `VFAT_MNT`
     values before generating the custom-mount benchmark source.
   - 2026-05-29 VFAT evidence follow-up: required VFAT mode removes stale
     `build/os/perf/VFAT4K.TXT` and the generated custom-mount benchmark source
     before input validation and readiness checks, so invalid or failed
     required runs cannot leave old ready/custom artifacts behind.
   - 2026-05-28 VFAT preparation path follow-up: the preparation helper applies
     the same mount path gate before creating the mount directory.
   - 2026-05-28 VFAT image path follow-up: the preparation helper rejects
     non-absolute or control-character `VFAT_IMG` values before creating the
     mount directory or image artifact.
   - 2026-05-28 VFAT image alias follow-up: the preparation helper rejects
     `VFAT_IMG` values that equal `VFAT_MNT` before creating or removing either
     path.
   - 2026-05-28 VFAT image containment follow-up: the preparation helper
     rejects `VFAT_IMG` values inside `VFAT_MNT` before creating the mount
     directory.
   - 2026-05-28 VFAT root path follow-up: the preparation helper rejects
     filesystem root as `VFAT_MNT` or `VFAT_IMG` before diagnosis or setup can
     treat `/` as a benchmark mount target or backing image path.
   - 2026-05-28 VFAT image parent follow-up: the preparation helper requires
     the `VFAT_IMG` parent directory to exist and be writable before diagnosis
     or setup creates the mount directory.
   - 2026-05-28 VFAT readiness follow-up:
     `VFAT_MNT=/tmp/simple_vfat_diag_codex_mnt VFAT_IMG=/tmp/simple_vfat_diag_codex.img scripts/perf/prepare-fat32-4k-vfat.shs --diagnose`
     passes as a non-mutating readiness probe. On this host it reports
     `vfat_prepare_diagnosis: not-ready`, `mountpoint: false`,
     `fstype: unknown`, `mkfs_fat: true`, `sudo_noninteractive: false`,
     `udisksctl: true`, `losetup: true`, and
     `reason: mount can be prepared if sudo or polkit authorizes loop mounting`.
     `sh -n scripts/perf/prepare-fat32-4k-vfat.shs &&
     sh -n scripts/perf/run-fat32-4k-cfat-baseline.shs` passes, and
     `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test
     test/01_unit/os/drivers/nvme/nvme_vfat_baseline_script_spec.spl
     --mode=interpreter --clean --format json` passes 9 examples, including
     the new no-artifact diagnostic path.
   - 2026-05-28 VFAT benchmark evidence follow-up: required VFAT mode now emits
     an unprivileged `vfat_baseline_evidence` block before failing, including
     mount path, source, filesystem type, mount options, seed readability,
     seed writability, and seed byte counts. On this host, a seeded non-VFAT
     spoof directory fails with `vfat_baseline_evidence: not-ready`,
     `vfat_fstype: btrfs`, `vfat_read_bytes: 32768`, and
     `vfat_write_bytes: 32768`, followed by the existing not-`vfat`/`msdos`
     rejection. When a real seeded VFAT mount is available, the same helper
     writes the ready evidence block to `build/os/perf/VFAT4K.TXT` before the
     repeated benchmark runs. The focused VFAT helper spec now passes 10
     examples with this failure-evidence coverage.
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
bin/simple test test/01_unit/os/services/vfs/vfs_pure_fat_production_guard_spec.spl --mode=interpreter --clean
bin/simple test test/01_unit/os/services/fat32/fat32_spec.spl --mode=interpreter --clean
bin/simple test test/02_integration/storage/dbfs/fat32_no_regression_spec.spl --mode=interpreter --clean
bin/simple test test/02_integration/storage/dbfs/dbfs_hw_passthrough_spec.spl --mode=interpreter --clean
bin/simple test test/01_unit/os/services/vfs/vfs_boot_nvme_lease_spec.spl --mode=interpreter --clean
bin/simple test test/01_unit/os/drivers/nvme/nvme_driver_probe_contract_spec.spl --mode=interpreter --clean
bin/simple test test/01_unit/os/drivers/nvme/nvme_performance_contract_spec.spl --mode=interpreter --clean
bin/simple test test/01_unit/os/drivers/nvme/nvme_vfat_baseline_script_spec.spl --mode=interpreter --clean
bin/simple test test/01_unit/os/drivers/nvme/nvme_physical_preflight_script_spec.spl --mode=interpreter --clean
bin/simple test test/01_unit/app/simpleos_nvme_serial_check_spec.spl --mode=interpreter --clean
bin/simple test test/01_unit/lib/fs_driver/fs_hardening_spec.spl --mode=interpreter --clean
bin/simple test test/03_system/storage_fat32_statfs_truncate_spec.spl --mode=interpreter --clean
bin/simple test test/03_system/storage_fat32_positional_cursor_spec.spl --mode=interpreter --clean
bin/simple test test/01_unit/os/port/host_fat32_tree_populator_spec.spl --mode=interpreter --clean
bin/simple check src/lib

# Physical acceptance, only on a host with an isolated same-controller user namespace:
sh scripts/os/run_simpleos_physical_nvme_perf.shs --preflight-scan --report-out /tmp/simpleos_nvme_preflight_scan.sdn --preflight-out /tmp/simpleos_nvme_preflight.sdn
scripts/perf/prepare-fat32-4k-vfat.shs
FAT32_4K_RUNS=3 REQUIRE_VFAT_BASELINE=1 scripts/perf/run-fat32-4k-cfat-baseline.shs
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
