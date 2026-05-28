# SimpleOS NVMe Filesystem Direct I/O Verification

Date: 2026-05-27

## Scope

Verification pass for the SimpleOS NVMe hardware-driver goal:

- one pure Simple NVMe driver surface usable by system and user-space namespace
  assignments,
- active-lease rejection for simultaneous incompatible system/user ownership,
- shared DirectIo interface for FAT32, NVFS, and DBFS,
- q35 proof that the Simple path is faster than the same-device C baseline.

## Evidence

Commands run against current working tree based on `origin/main` state
`9aeee55171` after the distinct user-namespace, shared-interface, and q35
marker gates were added:

```bash
src/compiler_rust/target/debug/simple test test/unit/os/drivers/nvme/nvme_storage_model_spec.spl --mode=interpreter --clean
src/compiler_rust/target/debug/simple test test/unit/os/drivers/nvme/nvme_namespace_assignment_spec.spl --mode=interpreter --clean
src/compiler_rust/target/debug/simple test test/unit/os/drivers/nvme/nvme_driver_probe_contract_spec.spl --mode=interpreter --clean
src/compiler_rust/target/debug/simple test test/unit/os/drivers/nvme/nvme_performance_contract_spec.spl --mode=interpreter --clean
src/compiler_rust/target/debug/simple test test/unit/os/services/vfs/nvme_block_adapter_spec.spl --mode=interpreter --clean
src/compiler_rust/target/debug/simple test test/unit/os/services/vfs/nvme_filesystem_mounts_spec.spl --mode=interpreter --clean
src/compiler_rust/target/debug/simple test test/unit/os/services/vfs/vfs_boot_nvme_lease_spec.spl --mode=interpreter --clean
src/compiler_rust/target/debug/simple test test/unit/os/kernel/boot/boot_fs_mount_acceptance_spec.spl --mode=interpreter --clean
src/compiler_rust/target/debug/simple test test/kernel/boot_fs_spec.spl --mode=interpreter --clean
src/compiler_rust/target/debug/simple test test/unit/os/drivers/real_device_readiness_spec.spl --mode=interpreter --clean
src/compiler_rust/target/debug/simple test test/unit/app/simpleos_nvme_serial_check_spec.spl --mode=interpreter --clean
src/compiler_rust/target/debug/simple test test/unit/os/qemu_runner_spec.spl --mode=interpreter --clean
src/compiler_rust/target/debug/simple test test/unit/os/port/simpleos_multiplatform_build_spec.spl --mode=interpreter --clean
src/compiler_rust/target/debug/simple os test --scenario x86_64-q35-pure-nvme-perf
```

Observed results:

- NVMe storage model: 23 passed.
- NVMe namespace assignment: 8 passed.
- NVMe driver probe contract: 6 passed.
- NVMe performance contract: 13 passed.
- NVMe block adapter: 7 passed.
- NVMe filesystem mounts: 16 passed.
- VFS boot NVMe lease and DirectIo contract: 26 passed.
- Boot filesystem mount acceptance: 9 passed.
- Boot filesystem state/spec: 11 passed.
- Real-device readiness: 8 passed.
- SimpleOS NVMe serial checker: 14 passed.
- QEMU runner: 28 passed.
- SimpleOS multiplatform build: 19 passed.
- q35 pure-NVMe perf: passed.

Current required q35 serial evidence shape:

```text
[real-device] storage_provider=simple-driver network_provider=simple-driver storage_placement=user-space-driver system_storage_placement=system-driver network_placement=user-space-driver storage_namespace=non-secure-resource-namespace network_namespace=non-secure-resource-namespace storage_grant=resource-grant-set:tok=nvme0 network_grant=resource-grant-set:tok=net0 common_driver_logic=shared
user_namespace_assignment=hardware-data-queue user_namespace_mode=user-assigned user_namespace_nsid=2 user_namespace_queue_id=2 user_namespace_active_lease_count=1 user_namespace_direct_io=read-write user_namespace_shared_interface=fat32,nvfs,dbfs user_namespace_conflict_policy=active-lease-checked
nvme_perf reason=ready simple_provider=simple-driver workload=4k-random-read-write io_size_bytes=4096 direct_io_path=nvme-lease-shared-dma-4k fs_consumers=fat32,nvfs,dbfs fat32_direct_io=read-write nvfs_direct_io=read-write dbfs_direct_io=read-write fat32_extent_source=freestanding-fat32-extents nvfs_extent_source=freestanding-dbfs-arena dbfs_extent_source=freestanding-dbfs-arena c_bridge_used=false c_baseline_scope=in-guest c_baseline_cache=direct common_logic_shared=true allocation_per_io=false simple_read_iops=1393 simple_write_iops=1488 simple_read_p99_us=7548 simple_write_p99_us=2732 c_read_iops=80 c_write_iops=130 c_read_p99_us=38520 c_write_p99_us=90928 queue_depth=128 warm_runs=3 max_rss_kib=1
TEST PASSED
```

## Requirement Status

- System/user namespace assignment: proven by namespace assignment and VFS active
  lease tests, including rejection of incompatible same-namespace ownership,
  rejection of user assignment to the active system namespace, discovery of a
  distinct assignable user namespace, and q35 evidence that a user data queue can
  perform direct 4K read/write on a user-assigned lease.
- Shared FAT32/NVFS/DBFS interface: proven by mount contracts, DirectIo extent
  mapping tests, q35 extent-source markers, the
  `user_namespace_shared_interface=fat32,nvfs,dbfs` serial marker, and
  `vfs_boot_nvme_shared_consumer_interface_reason`. The FAT32 hosted constructor
  is guarded to use `FsFat32Driver.new_with_direct_io`, retain its DirectIo
  capability, and delegate to the shared FAT32 cluster-chain extent mapper;
  NVFS/DBFS constructor paths are covered by device-backed extent tests.
- Pure Simple path faster than C FAT/NVMe baseline: proven by q35 same-device
  read/write IOPS and p99 comparison, with `c_bridge_used=false` on the Simple
  path, `allocation_per_io=false`, `c_baseline_scope=in-guest`, and
  `c_baseline_cache=direct`.

## Remaining Risk

The q35 freestanding proof intentionally avoids linking hosted filesystem driver
constructors into the tiny boot image. FAT32 uses a freestanding FAT fixture
extent path; NVFS and DBFS use their shared DBFS arena extent formula. Hosted
constructor/extent behavior is covered by unit-level FAT32 source guards and
NVFS/DBFS device-backed extent tests, not by the q35 freestanding image.
Representative real-NVMe hardware validation is still required before claiming
production throughput outside q35: queue depth, warm 4K random read/write
latency, max RSS, filesystem direct-I/O markers, and the Simple-vs-C baseline
need measurement on actual target devices. The acceptance gate for that evidence
now rejects emulator-only or incomplete reports unless they carry real-device
identity fields and user namespace evidence:
`hardware_target=real-nvme`, `qemu=false`, `device_model=...`,
`device_serial=...`, `namespace_nsid=...`, `measured_on=real-device`,
`user_namespace_assignment=hardware-data-queue`,
`user_namespace_mode=user-assigned`, `user_namespace_nsid=...`,
`user_namespace_queue_id=...`, `user_namespace_active_lease_count=...`,
`user_namespace_direct_io=read-write`,
`user_namespace_shared_interface=fat32,nvfs,dbfs`,
`user_namespace_conflict_policy=active-lease-checked`,
`fat32_direct_io=read-write`, `nvfs_direct_io=read-write`,
`dbfs_direct_io=read-write`, `c_baseline_scope=in-guest`, and
`c_baseline_cache=direct`.
Real-device runners now have the canonical helper
`nvme_real_hardware_perf_report_line_from_measurements` to produce that accepted
line from measured counters plus physical NVMe identity. The readiness layer now
has `real_device_physical_nvme_serial_acceptance_reason` to reject physical-run
logs unless they include pure Simple storage access, shared FAT32/NVFS/DBFS
direct-I/O markers, the distinct user namespace markers, and the real-NVMe
identity fields. An actual physical NVMe run remains pending. The same gate is
now exposed by
`src/app/simpleos_nvme_serial_check/main.spl --serial-log <path>` so captured
real hardware logs can be checked directly in the runner or lab workflow.
`scripts/run_simpleos_physical_nvme_perf.shs --serial-log <path>
--validate-log-only` is the canonical wrapper for checking an existing capture;
without `--validate-log-only` it captures from `SERIAL_PORT` first and then
delegates to the same checker. The wrapper also supports `--preflight` to verify
the checker runtime/app and a host-visible NVMe namespace device before capture.
For production lab use, `--production --preflight-out <path> --report-out <path>`
generates the host NVMe identity report and then validates that the SimpleOS
serial log reports the same model, serial, system namespace, and distinct user
namespace. The generated preflight path requires the host system namespace glob
to match exactly one namespace and a second same-controller namespace with a
different NSID to exist for user assignment; broad multi-device globs or missing
user namespaces are rejected as ambiguous production evidence.
