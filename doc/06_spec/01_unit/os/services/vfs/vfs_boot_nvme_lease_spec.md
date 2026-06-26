# Vfs Boot Nvme Lease Specification

> <details>

<!-- sdn-diagram:id=vfs_boot_nvme_lease_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vfs_boot_nvme_lease_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vfs_boot_nvme_lease_spec -> std
vfs_boot_nvme_lease_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vfs_boot_nvme_lease_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vfs Boot Nvme Lease Specification

## Scenarios

### VFS boot NVMe lease contract

#### builds a filesystem-ready system FAT32 lease for pure Simple boot

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lease = vfs_boot_nvme_system_fat32_lease(512u32, 65536u64, _tokenized_boot_grant())
expect(lease.provider).to_equal("simple-driver")
expect(lease.shared_block_interface).to_equal(true)
expect(lease.namespace_identity.nsid).to_equal(1u32)
expect(lease.lba_count).to_equal(65536u64)
expect(lease.grant_kind.to_start_with("resource-grant-set:tok=")).to_equal(true)
expect(nvme_filesystem_lease_reason(lease, NvmeFilesystemConsumer.Fat32)).to_equal("ready")
```

</details>

#### keeps invalid namespace geometry rejected before FAT32 can mount

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lease = vfs_boot_nvme_system_fat32_lease(0u32, 65536u64, _tokenized_boot_grant())
expect(nvme_filesystem_lease_reason(lease, NvmeFilesystemConsumer.Fat32)).to_equal("nvme-fs-namespace-invalid-lba-size")
```

</details>

#### builds production boot FAT32 leases only from ready transfer evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ready = nvme_transfer_evidence(
    "simple-driver",
    true,
    true,
    true,
    true,
    true,
    true,
    true,
    true,
    true,
    "system-driver",
    "kernel-owned-resource",
    "system-kernel-namespace",
    true,
    true
)
val missing_write = nvme_transfer_evidence(
    "simple-driver",
    true,
    true,
    true,
    true,
    true,
    true,
    false,
    true,
    true,
    "system-driver",
    "kernel-owned-resource",
    "system-kernel-namespace",
    true,
    true
)

val lease = vfs_boot_nvme_system_fat32_lease_from_transfer_evidence(512u32, 65536u64, ready).unwrap()
val rejected = vfs_boot_nvme_system_fat32_lease_from_transfer_evidence(512u32, 65536u64, missing_write)
expect(lease.provider).to_equal("simple-driver")
expect(nvme_filesystem_lease_reason(lease, NvmeFilesystemConsumer.Fat32)).to_equal("ready")
expect(rejected.unwrap_err()).to_equal("nvme-fs-transfer-not-ready:missing-nvme-sector-write")
```

</details>

#### uses hardware transfer evidence before mounting the pure Simple boot FAT32 lease

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/os/services/vfs/vfs_boot_init.spl")
expect(source.contains("val transfer_evidence_result = g_nvme.transfer_evidence_from_reversible_probe(")).to_equal(true)
expect(source.contains("\"system-driver\"")).to_equal(true)
expect(source.contains("\"kernel-owned-resource\"")).to_equal(true)
expect(source.contains("\"system-kernel-namespace\"")).to_equal(true)
expect(source.contains("vfs_boot_nvme_system_fat32_lease_from_transfer_evidence(")).to_equal(true)
expect(source.contains("g_vfs_nvme_active_leases = [lease]")).to_equal(true)
expect(source.contains("g_vfs_nvme_direct_adapter_leases = [lease]")).to_equal(true)
expect(source.contains("pure-Simple NVMe evidence lease policy degraded")).to_equal(true)
expect(source.contains("NvmeBlockAdapter.for_identified_namespace_unchecked(")).to_equal(true)
```

</details>

#### records boot NVMe leases and rejects later user assignment of the same namespace

1. vfs boot nvme reset active leases for test
   - Expected: vfs_boot_nvme_record_active_lease_for_test(system_lease) equals `ready`
   - Expected: vfs_boot_nvme_active_lease_count_for_test() equals `1u64`
   - Expected: vfs_boot_nvme_active_lease_acceptance_reason(conflicting_user) equals `nvme-fs-namespace-mode-conflict:system:user-assigned`
   - Expected: vfs_boot_nvme_active_lease_acceptance_reason(other_user) equals `ready`
2. vfs boot nvme reset active leases for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
vfs_boot_nvme_reset_active_leases_for_test()
val system_lease = vfs_boot_nvme_system_fat32_lease(512u32, 65536u64, _tokenized_boot_grant())
val conflicting_user = _user_lease_for_boot_nsid(1u32)
val other_user = _user_lease_for_boot_nsid(12u32)

expect(vfs_boot_nvme_record_active_lease_for_test(system_lease)).to_equal("ready")
expect(vfs_boot_nvme_active_lease_count_for_test()).to_equal(1u64)
expect(vfs_boot_nvme_active_lease_acceptance_reason(conflicting_user)).to_equal("nvme-fs-namespace-mode-conflict:system:user-assigned")
expect(vfs_boot_nvme_active_lease_acceptance_reason(other_user)).to_equal("ready")
vfs_boot_nvme_reset_active_leases_for_test()
```

</details>

#### assigns user namespaces through the active VFS lease registry

1. vfs boot nvme reset active leases for test
   - Expected: vfs_boot_nvme_record_active_lease_for_test(boot_lease) equals `ready`
   - Expected: conflict.unwrap_err() equals `nvme-fs-namespace-mode-conflict:system:user-assigned`
   - Expected: assigned.is_ok() is true
   - Expected: vfs_boot_nvme_active_lease_count_for_test() equals `2u64`
2. vfs boot nvme reset active leases for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
vfs_boot_nvme_reset_active_leases_for_test()
val boot_lease = vfs_boot_nvme_system_fat32_lease(512u32, 65536u64, _tokenized_boot_grant())
val grant = _tokenized_grant_for_owner(42u64)
val evidence = _user_evidence(grant)

expect(vfs_boot_nvme_record_active_lease_for_test(boot_lease)).to_equal("ready")
val conflict = vfs_boot_nvme_assign_user_namespace_lease(evidence, grant, 0u32, 1u32, 512u32, 65536u64, 0u64, 1024u64, SIMPLEOS_NVME_FIRST_DATA_QUEUE_ID, 42u64, 64u16, NvmeFilesystemConsumer.Nvfs)
val assigned = vfs_boot_nvme_assign_user_namespace_lease(evidence, grant, 0u32, 12u32, 512u32, 65536u64, 0u64, 1024u64, SIMPLEOS_NVME_FIRST_DATA_QUEUE_ID, 42u64, 64u16, NvmeFilesystemConsumer.Dbfs)

expect(conflict.unwrap_err()).to_equal("nvme-fs-namespace-mode-conflict:system:user-assigned")
expect(assigned.is_ok()).to_equal(true)
expect(vfs_boot_nvme_active_lease_count_for_test()).to_equal(2u64)
vfs_boot_nvme_reset_active_leases_for_test()
```

</details>

#### creates user namespace driver instances only after active-lease admission

1. vfs boot nvme reset active leases for test
   - Expected: vfs_boot_nvme_record_active_lease_for_test(boot_lease) equals `ready`
   - Expected: conflict.unwrap_err() equals `nvme-fs-namespace-mode-conflict:system:user-assigned`
   - Expected: vfs_boot_nvme_active_lease_count_for_test() equals `1u64`
   - Expected: mounted.is_ok() is true
   - Expected: vfs_boot_nvme_active_lease_count_for_test() equals `2u64`
2. vfs boot nvme reset active leases for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
vfs_boot_nvme_reset_active_leases_for_test()
val boot_lease = vfs_boot_nvme_system_fat32_lease(512u32, 65536u64, _tokenized_boot_grant())
val grant = _tokenized_grant_for_owner(42u64)
val evidence = _user_evidence(grant)

expect(vfs_boot_nvme_record_active_lease_for_test(boot_lease)).to_equal("ready")
val conflict = vfs_boot_nvme_assign_user_namespace_driver_instance("user-fat", MemBlockDevice.new(1024u64, 512u32), evidence, grant, 0u32, 1u32, 512u32, 65536u64, 0u64, 1024u64, SIMPLEOS_NVME_FIRST_DATA_QUEUE_ID, 42u64, 64u16, NvmeFilesystemConsumer.Fat32)
expect(conflict.unwrap_err()).to_equal("nvme-fs-namespace-mode-conflict:system:user-assigned")
expect(vfs_boot_nvme_active_lease_count_for_test()).to_equal(1u64)

val mounted = vfs_boot_nvme_assign_user_namespace_driver_instance("user-fat", MemBlockDevice.new(1024u64, 512u32), evidence, grant, 0u32, 13u32, 512u32, 65536u64, 0u64, 1024u64, SIMPLEOS_NVME_FIRST_DATA_QUEUE_ID, 42u64, 64u16, NvmeFilesystemConsumer.Fat32)
expect(mounted.is_ok()).to_equal(true)
expect(vfs_boot_nvme_active_lease_count_for_test()).to_equal(2u64)
vfs_boot_nvme_reset_active_leases_for_test()
```

</details>

#### keeps generic user namespace driver instances off the NVMe DirectIo adapter registry

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/os/services/vfs/vfs_boot_init.spl")
val generic_pos = source.index_of("fn vfs_boot_nvme_assign_user_namespace_driver_instance(")
val hardware_pos = source.index_of("fn vfs_boot_nvme_assign_user_namespace_hardware_driver_instance(")
val generic_body = source.substring(generic_pos, hardware_pos)

expect(generic_body.contains("vfs_nvme_buffered_driver_instance_for_lease(name, dev, lease, consumer)")).to_equal(true)
expect(generic_body.contains("vfs_nvme_driver_instance_for_lease(name, dev, lease, consumer)")).to_equal(false)
expect(generic_body.contains("g_vfs_nvme_direct_adapters = g_vfs_nvme_direct_adapters.push")).to_equal(false)
```

</details>

#### rejects a second user driver instance for the same namespace with a different grant

1. vfs boot nvme reset active leases for test
   - Expected: mounted.is_ok() is true
   - Expected: conflict.unwrap_err() equals `nvme-fs-user-namespace-grant-conflict`
   - Expected: vfs_boot_nvme_active_lease_count_for_test() equals `1u64`
2. vfs boot nvme reset active leases for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
vfs_boot_nvme_reset_active_leases_for_test()
val grant = _tokenized_grant_for_owner(42u64)
val other_grant = _tokenized_grant_for_owner(43u64)
val evidence = _user_evidence(grant)
val other_evidence = _user_evidence(other_grant)

val mounted = vfs_boot_nvme_assign_user_namespace_driver_instance("user-nvfs", MemBlockDevice.new(1024u64, 512u32), evidence, grant, 0u32, 21u32, 512u32, 65536u64, 0u64, 1024u64, SIMPLEOS_NVME_FIRST_DATA_QUEUE_ID, 42u64, 64u16, NvmeFilesystemConsumer.Nvfs)
val conflict = vfs_boot_nvme_assign_user_namespace_driver_instance("user-dbfs", MemBlockDevice.new(1024u64, 512u32), other_evidence, other_grant, 0u32, 21u32, 512u32, 65536u64, 0u64, 1024u64, SIMPLEOS_NVME_FIRST_DATA_QUEUE_ID + 1u16, 43u64, 64u16, NvmeFilesystemConsumer.Dbfs)

expect(mounted.is_ok()).to_equal(true)
expect(conflict.unwrap_err()).to_equal("nvme-fs-user-namespace-grant-conflict")
expect(vfs_boot_nvme_active_lease_count_for_test()).to_equal(1u64)
vfs_boot_nvme_reset_active_leases_for_test()
```

</details>

#### routes production user namespace mounts through the pure Simple NVMe block adapter

<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/os/services/vfs/vfs_boot_init.spl")
val lease_check_pos = source.index_of("val lease_result = nvme_user_assigned_filesystem_lease_from_grant_checked(")
val identify_pos = source.index_of("val identify = g_nvme.identify_namespace_id(lease.namespace_identity.nsid)")
val queue_pos = source.index_of("val queue_ready = g_nvme.ensure_user_data_queue_for_assignment(")
val adapter_pos = source.index_of("val adapter_result = NvmeBlockAdapter.for_filesystem_lease(g_nvme, lease, consumer)")
expect(source.contains("fn vfs_boot_nvme_assign_user_namespace_hardware_driver_instance(")).to_equal(true)
expect(source.contains("fn vfs_boot_nvme_assign_discovered_user_namespace_hardware_driver_instance(")).to_equal(true)
expect(source.contains("fn vfs_boot_nvme_system_namespace_nsid_for_user_assignment() -> u32:")).to_equal(true)
expect(source.contains("if lease.mode == NvmeNamespaceMode.System:")).to_equal(true)
expect(source.contains("val system_nsid = vfs_boot_nvme_system_namespace_nsid_for_user_assignment()")).to_equal(true)
expect(source.contains("val user_namespace = g_nvme.identify_first_assignable_user_namespace(system_nsid)")).to_equal(true)
expect(source.contains("\"nvme-user-assign-namespace-discovery-failed:\"")).to_equal(true)
expect(source.contains("facts.formatted_lba_size")).to_equal(true)
expect(source.contains("facts.lba_count")).to_equal(true)
expect(source.contains("val interface_probe = vfs_boot_nvme_assign_user_namespace_lease(")).to_equal(true)
expect(source.contains("val shared_interface = vfs_boot_nvme_shared_consumer_interface_reason(probe_lease)")).to_equal(true)
expect(source.contains("val release_probe = vfs_boot_nvme_release_active_lease(probe_lease)")).to_equal(true)
expect(source.contains("\"nvme-user-assign-shared-interface-not-ready:\"")).to_equal(true)
expect(source.contains("\"nvme-user-assign-probe-release-failed\"")).to_equal(true)
expect(source.contains("val driver_ready = vfs_boot_nvme_shared_driver_ready_for_user_assignment()")).to_equal(true)
expect(source.contains("return Err(driver_ready)")).to_equal(true)
expect(source.contains("val previous_nsid = g_nvme.get_namespace_id()")).to_equal(true)
expect(source.contains("val identify = g_nvme.identify_namespace_id(lease.namespace_identity.nsid)")).to_equal(true)
expect(source.contains("\"nvme-user-assign-namespace-identify-failed:\"")).to_equal(true)
expect(source.contains("val queue_ready = g_nvme.ensure_user_data_queue_for_assignment(")).to_equal(true)
expect(source.contains("lease.namespace_identity.controller_id")).to_equal(true)
expect(source.contains("lease.namespace_identity.nsid")).to_equal(true)
expect(source.contains("lease.queue.owner_task")).to_equal(true)
expect(source.contains("\"nvme-user-assign-queue-create-failed:\"")).to_equal(true)
expect(source.contains("val restore_identify = g_nvme.identify_namespace_id(previous_nsid)")).to_equal(true)
expect(source.contains("val restore_after_queue = g_nvme.identify_namespace_id(previous_nsid)")).to_equal(true)
expect(source.contains("val restore_after_adapter = g_nvme.identify_namespace_id(previous_nsid)")).to_equal(true)
expect(source.contains("\"nvme-user-assign-namespace-restore-failed:\"")).to_equal(true)
expect(source.contains("NvmeBlockAdapter.for_filesystem_lease(g_nvme, lease, consumer)")).to_equal(true)
expect(source.contains("val bounce = adapter.init_bounce_buffer()")).to_equal(true)
expect(source.contains("vfs_nvme_driver_instance_for_lease(name, adapter, lease, consumer)")).to_equal(true)
expect(source.contains("g_vfs_nvme_active_leases = g_vfs_nvme_active_leases.push(lease)")).to_equal(true)
expect(source.contains("g_vfs_nvme_direct_adapter_leases = g_vfs_nvme_direct_adapter_leases.push(lease)")).to_equal(true)
expect(source.contains("g_vfs_nvme_direct_adapters = g_vfs_nvme_direct_adapters.push(adapter)")).to_equal(true)
expect(lease_check_pos >= 0).to_equal(true)
expect(identify_pos > lease_check_pos).to_equal(true)
expect(queue_pos > lease_check_pos).to_equal(true)
expect(adapter_pos > lease_check_pos).to_equal(true)
```

</details>

#### keeps direct IO adapter ownership mapped by lease instead of active lease index

1. vfs boot nvme reset active leases for test
   - Expected: lease_only.is_ok() is true
   - Expected: vfs_boot_nvme_active_lease_count_for_test() equals `1u64`
   - Expected: vfs_boot_nvme_direct_adapter_count_for_test() equals `0u64`
   - Expected: source contains `var g_vfs_nvme_direct_adapter_leases: [NvmeFilesystemLease] = []`
   - Expected: source contains `for adapter_lease in g_vfs_nvme_direct_adapter_leases:`
   - Expected: source contains `nvme_filesystem_lease_same_identity(active, lease)`
   - Expected: source contains `nvme_filesystem_lease_same_identity(adapter_lease, lease)`
   - Expected: source contains `var removed_direct_adapter = false`
   - Expected: source contains `removed_direct_adapter = true`
   - Expected: source contains `remaining_adapter_leases = remaining_adapter_leases.push(adapter_lease)`
   - Expected: source contains `g_vfs_nvme_direct_adapter_leases = remaining_adapter_leases`
   - Expected: source contains `g_nvme.release_user_data_queue_owner(`
   - Expected: source contains `if lease.mode == NvmeNamespaceMode.UserAssigned and removed_direct_adapter:`
   - Expected: source contains `"nvme-fs-user-queue-owner-release-failed"`
   - Expected: source contains `lease.queue.queue_id`
   - Expected: source contains `lease.queue.owner_task`
   - Expected: source does not contain `for active in g_vfs_nvme_active_leases:\n        if nvme_filesystem_lease_sam... (full value in folded executable source)`
2. vfs boot nvme reset active leases for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
vfs_boot_nvme_reset_active_leases_for_test()
val grant = _tokenized_grant_for_owner(42u64)
val evidence = _user_evidence(grant)
val source = read_file("src/os/services/vfs/vfs_boot_init.spl")

val lease_only = vfs_boot_nvme_assign_user_namespace_lease(evidence, grant, 0u32, 16u32, 512u32, 65536u64, 0u64, 1024u64, SIMPLEOS_NVME_FIRST_DATA_QUEUE_ID, 42u64, 64u16, NvmeFilesystemConsumer.Nvfs)
expect(lease_only.is_ok()).to_equal(true)
expect(vfs_boot_nvme_active_lease_count_for_test()).to_equal(1u64)
expect(vfs_boot_nvme_direct_adapter_count_for_test()).to_equal(0u64)

expect(source.contains("var g_vfs_nvme_direct_adapter_leases: [NvmeFilesystemLease] = []")).to_equal(true)
expect(source.contains("for adapter_lease in g_vfs_nvme_direct_adapter_leases:")).to_equal(true)
expect(source.contains("nvme_filesystem_lease_same_identity(active, lease)")).to_equal(true)
expect(source.contains("nvme_filesystem_lease_same_identity(adapter_lease, lease)")).to_equal(true)
expect(source.contains("var removed_direct_adapter = false")).to_equal(true)
expect(source.contains("removed_direct_adapter = true")).to_equal(true)
expect(source.contains("remaining_adapter_leases = remaining_adapter_leases.push(adapter_lease)")).to_equal(true)
expect(source.contains("g_vfs_nvme_direct_adapter_leases = remaining_adapter_leases")).to_equal(true)
expect(source.contains("g_nvme.release_user_data_queue_owner(")).to_equal(true)
expect(source.contains("if lease.mode == NvmeNamespaceMode.UserAssigned and removed_direct_adapter:")).to_equal(true)
expect(source.contains("\"nvme-fs-user-queue-owner-release-failed\"")).to_equal(true)
expect(source.contains("lease.queue.queue_id")).to_equal(true)
expect(source.contains("lease.queue.owner_task")).to_equal(true)
expect(source.contains("for active in g_vfs_nvme_active_leases:\n        if nvme_filesystem_lease_same_assignment(active, lease):\n            if idx >= g_vfs_nvme_direct_adapters.len():")).to_equal(false)
vfs_boot_nvme_reset_active_leases_for_test()
```

</details>

#### requires filesystem DirectIo probe before submitting through lease adapters

1. vfs boot nvme reset active leases for test
2. owner: DmaOwner
   - Expected: vfs_boot_nvme_submit_filesystem_direct_4k(unsupported, lease, req).unwrap_err() equals `FsError.Unsupported`
   - Expected: vfs_boot_nvme_submit_filesystem_direct_4k(mounted, lease, unaligned).unwrap_err() equals `FsError.InvalidArg`
   - Expected: vfs_boot_nvme_submit_filesystem_direct_4k_batch(mounted_batch, lease, batch).unwrap_err() equals `FsError.NotFound`
3. vfs boot nvme reset active leases for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
vfs_boot_nvme_reset_active_leases_for_test()
val lease = _user_lease_for_boot_nsid(18u32)
val unsupported = DriverInstance.DbFs(DbFsDriver.new_hosted())
val mounted = vfs_nvme_driver_instance_for_lease("user-dbfs", MemBlockDevice.new(1024u64, 512u32), lease, NvmeFilesystemConsumer.Dbfs).unwrap()
val req = direct_io_read_request(7u64, 0i64, _valid_shared_dma_4k(), 100u32)
val unaligned = direct_io_read_request(7u64, 7i64, _valid_shared_dma_4k(), 100u32)
val batch = direct_io_read_batch_request(7u64, [0i64, 4096i64], SharedDmaBuffer(
    cpu_virt_addr: 0x1000u64,
    host_phys_addr: 0x2000u64,
    device_addr: 0x2000u64,
    byte_len: 8192u64,
    cache_policy: DmaCachePolicy.Coherent,
    owner: DmaOwner(task_id: 42u64, bdf_bus: 0u8, bdf_device: 4u8, bdf_function: 0u8),
    allocation_id: 10u64
), 100u32)

expect(vfs_boot_nvme_submit_filesystem_direct_4k(unsupported, lease, req).unwrap_err()).to_equal(FsError.Unsupported)
expect(vfs_boot_nvme_submit_filesystem_direct_4k(mounted, lease, unaligned).unwrap_err()).to_equal(FsError.InvalidArg)
val mounted_batch = vfs_nvme_driver_instance_for_lease("user-dbfs", MemBlockDevice.new(1024u64, 512u32), lease, NvmeFilesystemConsumer.Dbfs).unwrap()
expect(vfs_boot_nvme_submit_filesystem_direct_4k_batch(mounted_batch, lease, batch).unwrap_err()).to_equal(FsError.NotFound)
vfs_boot_nvme_reset_active_leases_for_test()
```

</details>

#### resolves filesystem DirectIo through file extents before lease adapter submission

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/os/services/vfs/vfs_boot_init.spl")

expect(source.contains("fn vfs_boot_nvme_map_filesystem_direct_4k_request(driver: DriverInstance, req: DirectIoRequest) -> Result<DirectIoRequest, FsError>:")).to_equal(true)
expect(source.contains("fn vfs_boot_nvme_map_filesystem_direct_4k_batch(driver: DriverInstance, req: DirectIoBatchRequest) -> Result<DirectIoBatchRequest, FsError>:")).to_equal(true)
expect(source.contains("driver.direct_io_extent_for_handle(FileHandle(id: req.handle_id), req.file_offset, 4096u64)")).to_equal(true)
expect(source.contains("val storage_offset = (mapped.storage_lba * mapped.sector_size.to_u64()) as i64")).to_equal(true)
expect(source.contains("file_offset: storage_offset")).to_equal(true)
expect(source.contains("for offset in req.file_offsets:\n        val extent = driver.direct_io_extent_for_handle(FileHandle(id: req.handle_id), offset, 4096u64)")).to_equal(true)
expect(source.contains("storage_offsets.push((mapped.storage_lba * mapped.sector_size.to_u64()) as i64)")).to_equal(true)
expect(source.contains("file_offsets: storage_offsets")).to_equal(true)
expect(source.contains("vfs_boot_nvme_direct_io_extent_matches_request(direct, mapped, req.file_offset, 4096u64)")).to_equal(true)
expect(source.contains("vfs_boot_nvme_direct_io_extent_matches_request(direct, mapped, offset, 4096u64)")).to_equal(true)
```

</details>

#### rejects DirectIo extents that do not match the probed request

<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dbfs = direct_io_nvme_filesystem_extension("dbfs", 512u32)
val matching = DirectIoExtent(
    consumer: "dbfs",
    file_offset: 0i64,
    storage_lba: 1u64,
    byte_len: 4096u64,
    sector_size: 512u32
)
val wrong_consumer = DirectIoExtent(
    consumer: "nvfs",
    file_offset: 0i64,
    storage_lba: 1u64,
    byte_len: 4096u64,
    sector_size: 512u32
)
val missing_consumer = DirectIoExtent(
    consumer: "",
    file_offset: 0i64,
    storage_lba: 1u64,
    byte_len: 4096u64,
    sector_size: 512u32
)
val wrong_offset = DirectIoExtent(
    consumer: "dbfs",
    file_offset: 4096i64,
    storage_lba: 1u64,
    byte_len: 4096u64,
    sector_size: 512u32
)
val wrong_len = DirectIoExtent(
    consumer: "dbfs",
    file_offset: 0i64,
    storage_lba: 1u64,
    byte_len: 8192u64,
    sector_size: 512u32
)

expect(vfs_boot_nvme_direct_io_extent_matches_request(dbfs, matching, 0i64, 4096u64)).to_equal(true)
expect(vfs_boot_nvme_direct_io_extent_matches_request(dbfs, wrong_consumer, 0i64, 4096u64)).to_equal(false)
expect(vfs_boot_nvme_direct_io_extent_matches_request(dbfs, missing_consumer, 0i64, 4096u64)).to_equal(false)
expect(vfs_boot_nvme_direct_io_extent_matches_request(dbfs, wrong_offset, 0i64, 4096u64)).to_equal(false)
expect(vfs_boot_nvme_direct_io_extent_matches_request(dbfs, wrong_len, 0i64, 4096u64)).to_equal(false)
```

</details>

#### exposes boot FAT DirectIo extents on the pure SimpleOS shared FAT driver

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/os/services/fat32/shared_fat32_driver.spl")

expect(source.contains("use std.fs_driver.direct_io.{DirectIoExtent}")).to_equal(true)
expect(source.contains("me fn direct_io_extent_for_handle(handle: u64, file_offset: i64, byte_len: u64) -> Result<DirectIoExtent, text>:")).to_equal(true)
expect(source.contains("return Result.Err(\"invalid file handle\")")).to_equal(true)
expect(source.contains("self.inner.direct_io_extent_for_handle(shared_opt.unwrap(), file_offset, byte_len)")).to_equal(true)
```

</details>

#### rejects uncommitted DBFS filesystem DirectIo batches before adapter lookup

1. owner: DmaOwner
   - Expected: mapped.unwrap_err() equals `FsError.Unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lease = _user_lease_for_boot_nsid(19u32)
val mounted = vfs_nvme_driver_instance_for_lease("user-dbfs", MemBlockDevice.new(1024u64, 512u32), lease, NvmeFilesystemConsumer.Dbfs).unwrap()
val handle = mounted.open_path(Path(raw: "/hot.db"), OpenFlags.read_write().with_create())
expect(handle.is_ok()).to_equal(true)
val batch = direct_io_read_batch_request(handle.unwrap().id, [0i64, 4096i64], SharedDmaBuffer(
    cpu_virt_addr: 0x1000u64,
    host_phys_addr: 0x2000u64,
    device_addr: 0x2000u64,
    byte_len: 8192u64,
    cache_policy: DmaCachePolicy.Coherent,
    owner: DmaOwner(task_id: 42u64, bdf_bus: 0u8, bdf_device: 4u8, bdf_function: 0u8),
    allocation_id: 11u64
), 100u32)
val mapped = vfs_boot_nvme_map_filesystem_direct_4k_batch(mounted, batch)
expect(mapped.unwrap_err()).to_equal(FsError.Unsupported)
```

</details>

#### rejects uncommitted NVFS filesystem DirectIo before adapter lookup

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lease = _user_lease_for_boot_nsid(20u32)
val mounted = vfs_nvme_driver_instance_for_lease("user-nvfs", MemBlockDevice.new(1024u64, 512u32), lease, NvmeFilesystemConsumer.Nvfs).unwrap()
val handle = mounted.open_path(Path(raw: "/hot.nvfs"), OpenFlags.read_write().with_create())
expect(handle.is_ok()).to_equal(true)
val single = direct_io_read_request(handle.unwrap().id, 4096i64, _valid_shared_dma_4k(), 100u32)
val mapped = vfs_boot_nvme_map_filesystem_direct_4k_request(mounted, single)
expect(mapped.unwrap_err()).to_equal(FsError.Unsupported)
```

</details>

#### wires q35 pure Simple perf evidence to real shared-DMA direct I/O

<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/os/services/vfs/vfs_boot_init.spl")
val entry = read_file("examples/09_embedded/simple_os/arch/x86_64/q35_pure_nvme_perf_entry.spl")

expect(source.contains("fn vfs_boot_nvme_q35_pure_simple_perf_probe_serial_lines() -> [text]:")).to_equal(true)
expect(source.contains("val batch_4k_ops: u32 = 32u32")).to_equal(true)
expect(source.contains("dma_alloc(batch_bytes as i64, DmaDir.Bidirectional)")).to_equal(true)
expect(source.contains("vfs_boot_nvme_submit_active_lease_direct_4k_batch(")).to_equal(true)
expect(source.contains("direct_io_read_batch_request(1u64, offsets, shared, 100000u32)")).to_equal(true)
expect(source.contains("direct_io_write_batch_request(1u64, offsets, shared, 100000u32)")).to_equal(true)
expect(source.contains("vfs_boot_nvme_submit_active_lease_direct_4k_batch_write_through(")).to_equal(true)
expect(source.contains("fn _vfs_boot_q35_ready_fs_consumers(lease: NvmeFilesystemLease) -> Result<text, text>:")).to_equal(true)
expect(source.contains("vfs_boot_nvme_shared_consumer_interface_reason(lease)")).to_equal(true)
expect(source.contains("nvme_filesystem_lease_reason(lease, NvmeFilesystemConsumer.Fat32)")).to_equal(true)
expect(source.contains("nvme_filesystem_lease_reason(lease, NvmeFilesystemConsumer.Nvfs)")).to_equal(true)
expect(source.contains("nvme_filesystem_lease_reason(lease, NvmeFilesystemConsumer.Dbfs)")).to_equal(true)
expect(source.contains("fs-consumer-lease-not-ready")).to_equal(true)
expect(source.contains("/SYS/PERF/CFAT4K.TXT")).to_equal(true)
expect(source.contains("real_device_q35_pure_simple_perf_marker_from_measurements(")).to_equal(true)
expect(source.contains("reason=c-baseline-missing-iops")).to_equal(true)
expect(entry.contains("q35_pure_nvme_perf_serial_lines")).to_equal(true)
expect(entry.contains("serial_println(line)")).to_equal(true)
val pcimgr = read_file("src/os/services/pcimgr/pcimgr.spl")
expect(pcimgr.contains("fn pcimgr_enable_mmio_bus_master")).to_equal(true)
expect(pcimgr.contains("command | 0x00000006u32")).to_equal(true)
expect(pcimgr.contains("pcimgr_enable_mmio_bus_master(bus_u8, dev_u8, func_u8)")).to_equal(true)
```

</details>

#### measures the standalone q35 C baseline inside the guest on the same device

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/os/services/vfs/q35_pure_nvme_perf_boot.spl")

expect(source.contains("extern fn simpleos_nvme_init() -> i64")).to_equal(true)
expect(source.contains("extern fn simpleos_nvme_read_sector(device_idx: u64, lba: u64, buf_addr: u64) -> i64")).to_equal(true)
expect(source.contains("extern fn simpleos_nvme_write_sector(device_idx: u64, lba: u64, buf_addr: u64) -> i64")).to_equal(true)
expect(source.contains("fn _measure_c_bridge_4k_baseline(lbas: [u64], sector_size: u32, buf_addr: u64) -> Result<Q35NvmePerfCounters, text>:")).to_equal(true)
expect(source.contains("val init = simpleos_nvme_init()")).to_equal(true)
expect(source.contains("simpleos_nvme_read_sector(0u64, lba + sector.to_u64(), buf_addr")).to_equal(true)
expect(source.contains("simpleos_nvme_write_sector(0u64, lba + sector.to_u64(), buf_addr")).to_equal(true)
expect(source.contains("all_lbas.push(lba)")).to_equal(true)
expect(source.contains("val c_baseline = _measure_c_bridge_4k_baseline(all_lbas, sector_size, shared.cpu_virt_addr)")).to_equal(true)
expect(source.contains("c_read_iops = c.read_iops")).to_equal(true)
expect(source.contains("c_write_iops = c.write_iops")).to_equal(true)
expect(source.contains("if read_p99_us >= c_read_p99_us:")).to_equal(true)
expect(source.contains("simple-read-p99-not-faster-than-c")).to_equal(true)
expect(source.contains("if write_p99_us >= c_write_p99_us:")).to_equal(true)
expect(source.contains("simple-write-p99-not-faster-than-c")).to_equal(true)
```

</details>

#### measures standalone q35 Simple I/O through the lease-backed adapter DirectIo surface

<details>
<summary>Executable SSpec</summary>

Runnable source: 57 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/os/services/vfs/q35_pure_nvme_perf_boot.spl")

expect(source.contains("use os.services.vfs.vfs_block_adapters.{NvmeBlockAdapter}")).to_equal(true)
expect(source.contains("nvme_transfer_readiness_reason(evidence)")).to_equal(true)
expect(source.contains("NvmeBlockAdapter.submit_direct_4k_shared_dma_batch_for_lease_window(nvme, 1u32, SIMPLEOS_NVME_SYSTEM_QUEUE_ID, consumer, 0u64, sector_count, sector_size, read_req)")).to_equal(true)
expect(source.contains("NvmeBlockAdapter.submit_direct_4k_shared_dma_batch_write_through_for_lease_window(nvme, 1u32, SIMPLEOS_NVME_SYSTEM_QUEUE_ID, consumer, 0u64, sector_count, sector_size, write_req)")).to_equal(true)
expect(source.contains("NvmeBlockAdapter.submit_direct_4k_shared_dma_batch_for_identified_namespace")).to_equal(false)
val adapter = read_file("src/os/services/vfs/vfs_block_adapters.spl")
expect(adapter.contains("static fn submit_direct_4k_shared_dma_batch_for_lease(")).to_equal(true)
expect(adapter.contains("static fn submit_direct_4k_shared_dma_batch_for_lease_window(")).to_equal(true)
expect(adapter.contains("static fn submit_direct_4k_shared_dma_batch_write_through_for_lease(")).to_equal(true)
expect(adapter.contains("static fn submit_direct_4k_shared_dma_batch_write_through_for_lease_window(")).to_equal(true)
expect(adapter.contains("nvme.flush_in_namespace_on_queue(lease.namespace_identity.nsid, lease.queue.queue_id)")).to_equal(true)
expect(adapter.contains("nvme.flush_in_namespace_on_queue(nsid, queue_id)")).to_equal(true)
expect(adapter.contains("durable: true")).to_equal(true)
expect(adapter.contains("durable: false")).to_equal(true)
expect(adapter.contains("lease: NvmeFilesystemLease")).to_equal(true)
expect(adapter.contains("val reason = nvme_filesystem_lease_reason(lease, consumer)")).to_equal(true)
expect(adapter.contains("nvme_filesystem_lease_absolute_lba(lease, relative_lba)")).to_equal(true)
expect(adapter.contains("if relative_lba >= lba_count:")).to_equal(true)
expect(adapter.contains("direct_io_validate_batch(ext, req, 4096u64)")).to_equal(true)
expect(source.contains("fn _fat32_fixture_direct_offsets(nvme: NvmeDriver, sector_size: u32, buf: SharedDmaBuffer) -> Result<[i64], text>:")).to_equal(true)
expect(source.contains("\"FAT4K   BIN\"")).to_equal(true)
expect(source.contains("fat32_extent_source=freestanding-fat32-extents")).to_equal(true)
expect(source.contains("fn _dbfs_arena_direct_offsets(sector_size: u32, sector_count: u64, arena_base_lba: u64) -> Result<[i64], text>:")).to_equal(true)
expect(source.contains("nvfs_extent_source=freestanding-dbfs-arena")).to_equal(true)
expect(source.contains("dbfs_extent_source=freestanding-dbfs-arena")).to_equal(true)
expect(source.contains("fat32_direct_io=read-write-through")).to_equal(true)
expect(source.contains("nvfs_direct_io=read-write-through")).to_equal(true)
expect(source.contains("dbfs_direct_io=read-write-through")).to_equal(true)
expect(source.contains("fn _consumer_for_measurement(run: u32, op: u32) -> NvmeFilesystemConsumer:")).to_equal(true)
expect(source.contains("saw_fat32 = true")).to_equal(true)
expect(source.contains("saw_nvfs = true")).to_equal(true)
expect(source.contains("saw_dbfs = true")).to_equal(true)
expect(source.contains("fs-consumer-direct-io-incomplete")).to_equal(true)
expect(source.contains("fs_consumers=\" + fs_consumers")).to_equal(true)
expect(source.contains("direct_io_read_batch_request(1u64, offsets, shared, 200000u32)")).to_equal(true)
expect(source.contains("direct_io_write_batch_request(1u64, offsets, shared, 200000u32)")).to_equal(true)
expect(source.contains("fn _q35_user_namespace_assignment_marker(")).to_equal(true)
expect(source.contains("active_leases: [NvmeFilesystemLease]")).to_equal(true)
expect(source.contains("val active_system_lease = _q35_system_namespace_lease(sector_size, sector_count)")).to_equal(true)
expect(source.contains("val system_nsid = 1u32")).to_equal(true)
expect(source.contains("val user_namespace = nvme.identify_first_assignable_user_namespace(system_nsid)")).to_equal(true)
expect(source.contains("val user_nsid = user_facts.nsid")).to_equal(true)
expect(source.contains("nvme_user_assigned_filesystem_lease_from_grant_checked(\n        evidence,\n        grant,\n        0u32,\n        1u32,")).to_equal(false)
expect(source.contains("nvme_user_assigned_filesystem_lease_from_grant_checked(\n        evidence,\n        grant,\n        0u32,\n        user_nsid,")).to_equal(true)
expect(source.contains("_q35_user_namespace_assignment_marker(nvme, grant, shared, [active_system_lease])")).to_equal(true)
expect(source.contains("NvmeFilesystemConsumer.Fat32,\n        []")).to_equal(false)
expect(source.contains("user_namespace_assignment=hardware-data-queue")).to_equal(true)
expect(source.contains("user_namespace_nsid=\" + lease.namespace_identity.nsid.to_u64().to_text()")).to_equal(true)
expect(source.contains("user_namespace_active_lease_count=\" + active_leases.len().to_u64().to_text()")).to_equal(true)
expect(source.contains("user_namespace_direct_io=read-write-through")).to_equal(true)
expect(source.contains("nvme_shared_filesystem_interface(lease)")).to_equal(true)
expect(source.contains("user_namespace_shared_interface=\" + nvme_shared_filesystem_interface_consumers()")).to_equal(true)
expect(source.contains("NvmeBlockAdapter.submit_direct_4k_shared_dma_batch_write_through_for_lease(")).to_equal(true)
expect(source.contains("nvme.read_4k_shared_dma_batch_in_namespace_on_queue(")).to_equal(false)
expect(source.contains("nvme.write_4k_shared_dma_batch_in_namespace_on_queue(")).to_equal(false)
```

</details>

#### packages the C FAT baseline artifact into the q35 FAT image contract

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = read_file("scripts/os/make_os_disk.shs")
expect(script.contains("SIMPLEOS_CFAT4K_BASELINE")).to_equal(true)
expect(script.contains("build\", \"os\", \"perf\", \"CFAT4K.TXT")).to_equal(true)
expect(script.contains("sys_entries.append(dir_entry(\"PERF       \"")).to_equal(true)
expect(script.contains("perf_entries.append(dir_entry(\"CFAT4K  TXT\"")).to_equal(true)
expect(script.contains("SIMPLEOS_FAT32_DIRECT_IO_4K_FIXTURE")).to_equal(true)
expect(script.contains("perf_entries.append(dir_entry(\"FAT4K   BIN\"")).to_equal(true)
expect(script.contains("spc = 8")).to_equal(true)
```

</details>

#### checks shared driver readiness before constructing hardware user namespace adapters

1. vfs boot nvme reset active leases for test
   - Expected: vfs_boot_nvme_shared_driver_ready_for_user_assignment() equals `nvme-user-assign-boot-storage-not-ready:not-mounted`
   - Expected: guard_pos >= 0 is true
   - Expected: adapter_pos > guard_pos is true
   - Expected: vfs_boot_nvme_active_lease_count_for_test() equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
vfs_boot_nvme_reset_active_leases_for_test()
val source = read_file("src/os/services/vfs/vfs_boot_init.spl")
val guard_pos = source.index_of("val driver_ready = vfs_boot_nvme_shared_driver_ready_for_user_assignment()")
val adapter_pos = source.index_of("NvmeBlockAdapter.for_filesystem_lease(g_nvme, lease, consumer)")

expect(vfs_boot_nvme_shared_driver_ready_for_user_assignment()).to_equal("nvme-user-assign-boot-storage-not-ready:not-mounted")
expect(guard_pos >= 0).to_equal(true)
expect(adapter_pos > guard_pos).to_equal(true)
expect(vfs_boot_nvme_active_lease_count_for_test()).to_equal(0u64)
```

</details>

#### releases user data queue owners on post-queue hardware assignment failures

<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/os/services/vfs/vfs_boot_init.spl")
val helper_pos = source.index_of("fn vfs_boot_nvme_release_user_queue_owner_for_failed_assignment(lease: NvmeFilesystemLease) -> text:")
val fn_start = source.index_of("fn vfs_boot_nvme_assign_user_namespace_hardware_driver_instance(")
val fn_end = source.index_of("fn vfs_boot_nvme_assign_discovered_user_namespace_hardware_driver_instance(")
val body = source.substring(fn_start, fn_end)
val queue_pos = body.index_of("val queue_ready = g_nvme.ensure_user_data_queue_for_assignment(")
val adapter_fail_pos = body.index_of("if adapter_result.is_err():")
val bounce_fail_pos = body.index_of("if bounce.is_err():")
val driver_fail_pos = body.index_of("if driver_result.is_err():")
val record_pos = body.index_of("g_vfs_nvme_active_leases = g_vfs_nvme_active_leases.push(lease)")
val adapter_fail_body = body.substring(adapter_fail_pos, bounce_fail_pos)
val bounce_fail_body = body.substring(bounce_fail_pos, driver_fail_pos)
val driver_fail_body = body.substring(driver_fail_pos, record_pos)

expect(helper_pos >= 0).to_equal(true)
expect(fn_start >= 0).to_equal(true)
expect(fn_end > fn_start).to_equal(true)
expect(source.contains("g_nvme.release_user_data_queue_owner(\n        lease.queue.queue_id,\n        lease.namespace_identity.controller_id,\n        lease.namespace_identity.nsid,\n        lease.queue.owner_task\n    )")).to_equal(true)
expect(adapter_fail_pos > queue_pos).to_equal(true)
expect(bounce_fail_pos > queue_pos).to_equal(true)
expect(driver_fail_pos > queue_pos).to_equal(true)
expect(adapter_fail_pos < record_pos).to_equal(true)
expect(bounce_fail_pos < record_pos).to_equal(true)
expect(driver_fail_pos < record_pos).to_equal(true)
expect(adapter_fail_body.index_of("val restore_after_adapter = g_nvme.identify_namespace_id(previous_nsid)") < adapter_fail_body.index_of("val queue_release = vfs_boot_nvme_release_user_queue_owner_for_failed_assignment(lease)")).to_equal(true)
expect(adapter_fail_body.contains("vfs_boot_nvme_release_user_queue_owner_for_failed_assignment(lease)")).to_equal(true)
expect(bounce_fail_body.contains("vfs_boot_nvme_release_user_queue_owner_for_failed_assignment(lease)")).to_equal(true)
expect(driver_fail_body.contains("vfs_boot_nvme_release_user_queue_owner_for_failed_assignment(lease)")).to_equal(true)
```

</details>

#### releases active user namespace leases so reassignment can proceed

1. vfs boot nvme reset active leases for test
   - Expected: vfs_boot_nvme_active_lease_count_for_test() equals `1u64`
   - Expected: vfs_boot_nvme_release_active_lease(missing) equals `nvme-fs-active-lease-not-found`
   - Expected: vfs_boot_nvme_active_lease_count_for_test() equals `1u64`
   - Expected: vfs_boot_nvme_release_active_lease(assigned) equals `ready`
   - Expected: vfs_boot_nvme_active_lease_count_for_test() equals `0u64`
   - Expected: reassigned.is_ok() is true
   - Expected: vfs_boot_nvme_active_lease_count_for_test() equals `1u64`
2. vfs boot nvme reset active leases for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
vfs_boot_nvme_reset_active_leases_for_test()
val grant = _tokenized_grant_for_owner(42u64)
val evidence = _user_evidence(grant)
val assigned = vfs_boot_nvme_assign_user_namespace_lease(evidence, grant, 0u32, 14u32, 512u32, 65536u64, 0u64, 1024u64, SIMPLEOS_NVME_FIRST_DATA_QUEUE_ID, 42u64, 64u16, NvmeFilesystemConsumer.Nvfs).unwrap()
val missing = _user_lease_for_boot_nsid(15u32)

expect(vfs_boot_nvme_active_lease_count_for_test()).to_equal(1u64)
expect(vfs_boot_nvme_release_active_lease(missing)).to_equal("nvme-fs-active-lease-not-found")
expect(vfs_boot_nvme_active_lease_count_for_test()).to_equal(1u64)
expect(vfs_boot_nvme_release_active_lease(assigned)).to_equal("ready")
expect(vfs_boot_nvme_active_lease_count_for_test()).to_equal(0u64)
val reassigned = vfs_boot_nvme_assign_user_namespace_lease(evidence, grant, 0u32, 14u32, 512u32, 65536u64, 0u64, 1024u64, SIMPLEOS_NVME_FIRST_DATA_QUEUE_ID, 42u64, 64u16, NvmeFilesystemConsumer.Nvfs)
expect(reassigned.is_ok()).to_equal(true)
expect(vfs_boot_nvme_active_lease_count_for_test()).to_equal(1u64)
vfs_boot_nvme_reset_active_leases_for_test()
```

</details>

#### accepts only pure Simple NVMe boot storage as production-ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(vfs_boot_storage_acceptance_reason(false, "not-mounted", false)).to_equal("not-mounted")
expect(vfs_boot_storage_acceptance_reason(true, "c-boot-bridge", false)).to_equal("vfs-boot-storage-not-pure-simple:c-boot-bridge")
expect(vfs_boot_storage_acceptance_reason(true, "virtio-blk", true)).to_equal("vfs-boot-storage-not-nvme-simple-driver:virtio-blk")
expect(vfs_boot_storage_acceptance_reason(true, "simple-driver", true)).to_equal("ready")
expect(vfs_boot_storage_production_ready(true, "c-boot-bridge", false)).to_equal(false)
expect(vfs_boot_storage_production_ready(true, "virtio-blk", true)).to_equal(false)
expect(vfs_boot_storage_production_ready(true, "simple-driver", true)).to_equal(true)
```

</details>

#### keeps production VFS boot out of C bridge and virtio fallback branches

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/os/services/vfs/vfs_boot_init.spl")
val boot_pos = source.index_of("pub fn vfs_boot_init() -> bool:")
val production_pos = source.index_of("pub fn vfs_boot_init_production() -> bool:")
val pure_pos = source.index_of("fn _vfs_boot_init_pure_nvme_fat32")
val boot_body = source.substring(boot_pos, production_pos)
val production_body = source.substring(production_pos, pure_pos)

expect(boot_body.contains("init_c_bridge()")).to_equal(false)
expect(boot_body.contains("_vfs_boot_init_virtio_fat32()")).to_equal(false)
expect(boot_body.contains("pure-Simple NVMe + FAT32 unavailable; VFS unavailable")).to_equal(true)
expect(production_body.contains("vfs_boot_init()")).to_equal(false)
expect(production_body.contains("init_c_bridge()")).to_equal(false)
expect(production_body.contains("_vfs_boot_init_virtio_fat32()")).to_equal(false)
expect(production_body.contains("_vfs_boot_init_pure_nvme_fat32(nvme_idx.to_u64())")).to_equal(true)
```

</details>

#### exports fail-closed production readiness through the VFS public surface

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(vfs_boot_storage_acceptance_ready()).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/services/vfs/vfs_boot_nvme_lease_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- VFS boot NVMe lease contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
