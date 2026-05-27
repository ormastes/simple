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
`0d888851e8` plus the q35 user-namespace proof update:

```bash
src/compiler_rust/target/debug/simple test test/unit/os/drivers/nvme/nvme_namespace_assignment_spec.spl --mode=interpreter --clean
src/compiler_rust/target/debug/simple test test/unit/os/drivers/nvme/nvme_driver_probe_contract_spec.spl --mode=interpreter --clean
src/compiler_rust/target/debug/simple test test/unit/os/services/vfs/nvme_block_adapter_spec.spl --mode=interpreter --clean
src/compiler_rust/target/debug/simple test test/unit/os/services/vfs/nvme_filesystem_mounts_spec.spl --mode=interpreter --clean
src/compiler_rust/target/debug/simple test test/unit/os/services/vfs/vfs_boot_nvme_lease_spec.spl --mode=interpreter --clean
src/compiler_rust/target/debug/simple test test/unit/os/kernel/boot/boot_fs_mount_acceptance_spec.spl --mode=interpreter --clean
src/compiler_rust/target/debug/simple test test/kernel/boot_fs_spec.spl --mode=interpreter --clean
src/compiler_rust/target/debug/simple os test --scenario x86_64-q35-pure-nvme-perf
```

Observed results:

- NVMe namespace assignment: 8 passed.
- NVMe driver probe contract: 6 passed.
- NVMe block adapter: 7 passed.
- NVMe filesystem mounts: 12 passed.
- VFS boot NVMe lease and DirectIo contract: 23 passed.
- Boot filesystem mount acceptance: 9 passed.
- Boot filesystem state/spec: 11 passed.
- q35 pure-NVMe perf: passed.

Latest q35 serial evidence:

```text
[real-device] storage_provider=simple-driver network_provider=simple-driver storage_placement=user-space-driver network_placement=user-space-driver storage_namespace=non-secure-resource-namespace network_namespace=non-secure-resource-namespace storage_grant=resource-grant-set:tok=nvme0 network_grant=resource-grant-set:tok=net0 common_driver_logic=shared
user_namespace_assignment=hardware-data-queue user_namespace_mode=user-assigned user_namespace_queue_id=2 user_namespace_direct_io=read-write user_namespace_conflict_policy=active-lease-checked
nvme_perf reason=ready simple_provider=simple-driver workload=4k-random-read-write io_size_bytes=4096 direct_io_path=nvme-lease-shared-dma-4k fs_consumers=fat32,nvfs,dbfs fat32_extent_source=freestanding-fat32-extents nvfs_extent_source=freestanding-dbfs-arena dbfs_extent_source=freestanding-dbfs-arena c_bridge_used=false common_logic_shared=true allocation_per_io=false simple_read_iops=1625 simple_write_iops=1868 simple_read_p99_us=6800 simple_write_p99_us=2296 c_read_iops=96 c_write_iops=154 c_read_p99_us=13056 c_write_p99_us=8728 queue_depth=128 warm_runs=3 max_rss_kib=1
TEST PASSED
```

## Requirement Status

- System/user namespace assignment: proven by namespace assignment and VFS active
  lease tests, including rejection of incompatible same-namespace ownership, and
  by q35 hardware evidence that queue 2 is created as a user data queue and can
  perform direct 4K read/write on a user-assigned lease.
- Shared FAT32/NVFS/DBFS interface: proven by mount contracts, DirectIo extent
  mapping tests, and q35 extent-source markers. The FAT32 hosted constructor is
  guarded to use `FsFat32Driver.new_with_direct_io`, retain its DirectIo
  capability, and delegate to the shared FAT32 cluster-chain extent mapper;
  NVFS/DBFS constructor paths are covered by device-backed extent tests.
- Pure Simple path faster than C FAT/NVMe baseline: proven by q35 same-device
  read/write IOPS and p99 comparison, with `c_bridge_used=false` on the Simple
  path and `allocation_per_io=false`.

## Remaining Risk

The q35 freestanding proof intentionally avoids linking hosted filesystem driver
constructors into the tiny boot image. FAT32 uses a freestanding FAT fixture
extent path; NVFS and DBFS use their shared DBFS arena extent formula. Hosted
constructor/extent behavior is covered by unit-level FAT32 source guards and
NVFS/DBFS device-backed extent tests, not by the q35 freestanding image.
