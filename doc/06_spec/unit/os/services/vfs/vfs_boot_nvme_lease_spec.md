# Vfs Boot Nvme Lease Specification

> Tests covering VFS boot NVMe lease contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vfs Boot Nvme Lease Specification

## Scenarios

### VFS boot NVMe lease contract

#### builds a filesystem-ready system FAT32 lease for pure Simple boot

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- builds a filesystem-ready system FAT32 lease for pure Simple boot


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds a filesystem-ready system FAT32 lease for pure Simple boot")
val lease = vfs_boot_nvme_system_fat32_lease(512u32, 65536u64, _tokenized_boot_grant())
assert_equal(lease.provider, "simple-driver")
assert_equal(lease.shared_block_interface, true)
assert_equal(lease.namespace_identity.nsid, 1u32)
assert_equal(lease.lba_count, 65536u64)
assert_equal(lease.grant_kind.to_start_with("resource-grant-set:tok="), true)
assert_equal(nvme_filesystem_lease_reason(lease, NvmeFilesystemConsumer.Fat32), "ready")
```

</details>

#### keeps invalid namespace geometry rejected before FAT32 can mount

- keeps invalid namespace geometry rejected before FAT32 can mount


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps invalid namespace geometry rejected before FAT32 can mount")
val lease = vfs_boot_nvme_system_fat32_lease(0u32, 65536u64, _tokenized_boot_grant())
assert_equal(nvme_filesystem_lease_reason(lease, NvmeFilesystemConsumer.Fat32), "nvme-fs-namespace-invalid-lba-size")
```

</details>

#### builds production boot FAT32 leases only from ready transfer evidence

- builds production boot FAT32 leases only from ready transfer evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds production boot FAT32 leases only from ready transfer evidence")
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
assert_equal(lease.provider, "simple-driver")
assert_equal(nvme_filesystem_lease_reason(lease, NvmeFilesystemConsumer.Fat32), "ready")
assert_equal(rejected.unwrap_err(), "nvme-fs-transfer-not-ready:missing-nvme-sector-write")
```

</details>

#### uses hardware transfer evidence before mounting the pure Simple boot FAT32 lease

- uses hardware transfer evidence before mounting the pure Simple boot FAT32 lease


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses hardware transfer evidence before mounting the pure Simple boot FAT32 lease")
val source = (read_file("src/os/services/vfs/vfs_boot_init.spl") + read_file("src/os/services/vfs/vfs_boot_core.spl") + read_file("src/os/services/vfs/vfs_boot_state.spl") + read_file("src/os/services/vfs/vfs_ambient_context.spl") + read_file("src/os/services/vfs/nvme_boot_runtime_owner.spl") + read_file("src/os/services/vfs/nvme_filesystem_direct_io.spl") + read_file("src/os/services/vfs/nvme_q35_lease_perf.spl") + read_file("src/os/services/vfs/direct_fat32_boot_reader.spl"))
assert_equal(source.contains("val transfer_evidence_result = g_nvme.transfer_evidence_from_reversible_probe("), true)
assert_equal(source.contains("\"system-driver\""), true)
assert_equal(source.contains("\"kernel-owned-resource\""), true)
assert_equal(source.contains("\"system-kernel-namespace\""), true)
assert_equal(source.contains("vfs_boot_nvme_system_fat32_lease_from_transfer_evidence("), true)
assert_equal(source.contains("g_vfs_nvme_active_leases = [lease]"), true)
assert_equal(source.contains("g_vfs_nvme_direct_adapter_leases = [lease]"), true)
assert_equal(source.contains("pure-Simple NVMe evidence lease policy degraded"), true)
assert_equal(source.contains("NvmeBlockAdapter.for_identified_namespace_unchecked("), true)
```

</details>

#### records boot NVMe leases and rejects later user assignment of the same namespace

- records boot NVMe leases and rejects later user assignment of the same namespace


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records boot NVMe leases and rejects later user assignment of the same namespace")
vfs_boot_nvme_reset_active_leases_for_test()
val system_lease = vfs_boot_nvme_system_fat32_lease(512u32, 65536u64, _tokenized_boot_grant())
val conflicting_user = _user_lease_for_boot_nsid(1u32)
val other_user = _user_lease_for_boot_nsid(12u32)

assert_equal(vfs_boot_nvme_record_active_lease_for_test(system_lease), "ready")
assert_equal(vfs_boot_nvme_active_lease_count_for_test(), 1u64)
assert_equal(vfs_boot_nvme_active_lease_acceptance_reason(conflicting_user), "nvme-fs-namespace-mode-conflict:system:user-assigned")
assert_equal(vfs_boot_nvme_active_lease_acceptance_reason(other_user), "ready")
vfs_boot_nvme_reset_active_leases_for_test()
```

</details>

#### assigns user namespaces through the active VFS lease registry

- assigns user namespaces through the active VFS lease registry


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns user namespaces through the active VFS lease registry")
vfs_boot_nvme_reset_active_leases_for_test()
val boot_lease = vfs_boot_nvme_system_fat32_lease(512u32, 65536u64, _tokenized_boot_grant())
val grant = _tokenized_grant_for_owner(42u64)
val evidence = _user_evidence(grant)

assert_equal(vfs_boot_nvme_record_active_lease_for_test(boot_lease), "ready")
val conflict = vfs_boot_nvme_assign_user_namespace_lease(evidence, grant, 0u32, 1u32, 512u32, 65536u64, 0u64, 1024u64, SIMPLEOS_NVME_FIRST_DATA_QUEUE_ID, 42u64, 64u16, NvmeFilesystemConsumer.Nvfs)
val assigned = vfs_boot_nvme_assign_user_namespace_lease(evidence, grant, 0u32, 12u32, 512u32, 65536u64, 0u64, 1024u64, SIMPLEOS_NVME_FIRST_DATA_QUEUE_ID, 42u64, 64u16, NvmeFilesystemConsumer.Dbfs)

assert_equal(conflict.unwrap_err(), "nvme-fs-namespace-mode-conflict:system:user-assigned")
assert_equal(assigned.is_ok(), true)
assert_equal(vfs_boot_nvme_active_lease_count_for_test(), 2u64)
vfs_boot_nvme_reset_active_leases_for_test()
```

</details>

#### creates user namespace driver instances only after active-lease admission

- creates user namespace driver instances only after active-lease admission


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates user namespace driver instances only after active-lease admission")
vfs_boot_nvme_reset_active_leases_for_test()
val boot_lease = vfs_boot_nvme_system_fat32_lease(512u32, 65536u64, _tokenized_boot_grant())
val grant = _tokenized_grant_for_owner(42u64)
val evidence = _user_evidence(grant)

assert_equal(vfs_boot_nvme_record_active_lease_for_test(boot_lease), "ready")
val conflict = vfs_boot_nvme_assign_user_namespace_driver_instance("user-fat", MemBlockDevice.new(1024u64, 512u32), evidence, grant, 0u32, 1u32, 512u32, 65536u64, 0u64, 1024u64, SIMPLEOS_NVME_FIRST_DATA_QUEUE_ID, 42u64, 64u16, NvmeFilesystemConsumer.Fat32)
assert_equal(conflict.unwrap_err(), "nvme-fs-namespace-mode-conflict:system:user-assigned")
assert_equal(vfs_boot_nvme_active_lease_count_for_test(), 1u64)

val mounted = vfs_boot_nvme_assign_user_namespace_driver_instance("user-fat", MemBlockDevice.new(1024u64, 512u32), evidence, grant, 0u32, 13u32, 512u32, 65536u64, 0u64, 1024u64, SIMPLEOS_NVME_FIRST_DATA_QUEUE_ID, 42u64, 64u16, NvmeFilesystemConsumer.Fat32)
assert_equal(mounted.is_ok(), true)
assert_equal(vfs_boot_nvme_active_lease_count_for_test(), 2u64)
vfs_boot_nvme_reset_active_leases_for_test()
```

</details>

#### keeps generic user namespace driver instances off the NVMe DirectIo adapter registry

- keeps generic user namespace driver instances off the NVMe DirectIo adapter registry


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps generic user namespace driver instances off the NVMe DirectIo adapter registry")
val source = (read_file("src/os/services/vfs/vfs_boot_init.spl") + read_file("src/os/services/vfs/vfs_boot_core.spl") + read_file("src/os/services/vfs/vfs_boot_state.spl") + read_file("src/os/services/vfs/vfs_ambient_context.spl") + read_file("src/os/services/vfs/nvme_boot_runtime_owner.spl") + read_file("src/os/services/vfs/nvme_filesystem_direct_io.spl") + read_file("src/os/services/vfs/nvme_q35_lease_perf.spl") + read_file("src/os/services/vfs/direct_fat32_boot_reader.spl"))
val generic_pos = source.index_of("fn vfs_boot_nvme_assign_user_namespace_driver_instance(")
val hardware_pos = source.index_of("fn vfs_boot_nvme_assign_user_namespace_hardware_driver_instance(")
val generic_body = source.substring(generic_pos, hardware_pos)

assert_equal(generic_body.contains("vfs_nvme_buffered_driver_instance_for_lease(name, dev, lease, consumer)"), true)
assert_equal(generic_body.contains("vfs_nvme_driver_instance_for_lease(name, dev, lease, consumer)"), false)
assert_equal(generic_body.contains("g_vfs_nvme_direct_adapters = g_vfs_nvme_direct_adapters.push"), false)
```

</details>

#### rejects a second user driver instance for the same namespace with a different grant

- rejects a second user driver instance for the same namespace with a different grant


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a second user driver instance for the same namespace with a different grant")
vfs_boot_nvme_reset_active_leases_for_test()
val grant = _tokenized_grant_for_owner(42u64)
val other_grant = _tokenized_grant_for_owner(43u64)
val evidence = _user_evidence(grant)
val other_evidence = _user_evidence(other_grant)

val mounted = vfs_boot_nvme_assign_user_namespace_driver_instance("user-nvfs", MemBlockDevice.new(1024u64, 512u32), evidence, grant, 0u32, 21u32, 512u32, 65536u64, 0u64, 1024u64, SIMPLEOS_NVME_FIRST_DATA_QUEUE_ID, 42u64, 64u16, NvmeFilesystemConsumer.Nvfs)
val conflict = vfs_boot_nvme_assign_user_namespace_driver_instance("user-dbfs", MemBlockDevice.new(1024u64, 512u32), other_evidence, other_grant, 0u32, 21u32, 512u32, 65536u64, 0u64, 1024u64, SIMPLEOS_NVME_FIRST_DATA_QUEUE_ID + 1u16, 43u64, 64u16, NvmeFilesystemConsumer.Dbfs)

assert_equal(mounted.is_ok(), true)
assert_equal(conflict.unwrap_err(), "nvme-fs-user-namespace-grant-conflict")
assert_equal(vfs_boot_nvme_active_lease_count_for_test(), 1u64)
vfs_boot_nvme_reset_active_leases_for_test()
```

</details>

#### routes production user namespace mounts through the pure Simple NVMe block adapter

- routes production user namespace mounts through the pure Simple NVMe block adapter


<details>
<summary>Executable SSpec</summary>

Runnable source: 45 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes production user namespace mounts through the pure Simple NVMe block adapter")
val source = (read_file("src/os/services/vfs/vfs_boot_init.spl") + read_file("src/os/services/vfs/vfs_boot_core.spl") + read_file("src/os/services/vfs/vfs_boot_state.spl") + read_file("src/os/services/vfs/vfs_ambient_context.spl") + read_file("src/os/services/vfs/nvme_boot_runtime_owner.spl") + read_file("src/os/services/vfs/nvme_filesystem_direct_io.spl") + read_file("src/os/services/vfs/nvme_q35_lease_perf.spl") + read_file("src/os/services/vfs/direct_fat32_boot_reader.spl"))
val lease_check_pos = source.index_of("val lease_result = nvme_user_assigned_filesystem_lease_from_grant_checked(")
val identify_pos = source.index_of("val identify = g_nvme.identify_namespace_id(lease.namespace_identity.nsid)")
val queue_pos = source.index_of("val queue_ready = g_nvme.ensure_user_data_queue_for_assignment(")
val adapter_pos = source.index_of("val adapter_result = NvmeBlockAdapter.for_filesystem_lease(g_nvme, lease, consumer)")
assert_equal(source.contains("fn vfs_boot_nvme_assign_user_namespace_hardware_driver_instance("), true)
assert_equal(source.contains("fn vfs_boot_nvme_assign_discovered_user_namespace_hardware_driver_instance("), true)
assert_equal(source.contains("fn vfs_boot_nvme_system_namespace_nsid_for_user_assignment() -> u32:"), true)
assert_equal(source.contains("if lease.mode == NvmeNamespaceMode.System:"), true)
assert_equal(source.contains("val system_nsid = vfs_boot_nvme_system_namespace_nsid_for_user_assignment()"), true)
assert_equal(source.contains("val user_namespace = g_nvme.identify_first_assignable_user_namespace(system_nsid)"), true)
assert_equal(source.contains("\"nvme-user-assign-namespace-discovery-failed:\""), true)
assert_equal(source.contains("facts.formatted_lba_size"), true)
assert_equal(source.contains("facts.lba_count"), true)
assert_equal(source.contains("val interface_probe = vfs_boot_nvme_assign_user_namespace_lease("), true)
assert_equal(source.contains("val shared_interface = vfs_boot_nvme_shared_consumer_interface_reason(probe_lease)"), true)
assert_equal(source.contains("val release_probe = vfs_boot_nvme_release_active_lease(probe_lease)"), true)
assert_equal(source.contains("\"nvme-user-assign-shared-interface-not-ready:\""), true)
assert_equal(source.contains("\"nvme-user-assign-probe-release-failed\""), true)
assert_equal(source.contains("val driver_ready = vfs_boot_nvme_shared_driver_ready_for_user_assignment()"), true)
assert_equal(source.contains("return Err(driver_ready)"), true)
assert_equal(source.contains("val previous_nsid = g_nvme.get_namespace_id()"), true)
assert_equal(source.contains("val identify = g_nvme.identify_namespace_id(lease.namespace_identity.nsid)"), true)
assert_equal(source.contains("\"nvme-user-assign-namespace-identify-failed:\""), true)
assert_equal(source.contains("val queue_ready = g_nvme.ensure_user_data_queue_for_assignment("), true)
assert_equal(source.contains("lease.namespace_identity.controller_id"), true)
assert_equal(source.contains("lease.namespace_identity.nsid"), true)
assert_equal(source.contains("lease.queue.owner_task"), true)
assert_equal(source.contains("\"nvme-user-assign-queue-create-failed:\""), true)
assert_equal(source.contains("val restore_identify = g_nvme.identify_namespace_id(previous_nsid)"), true)
assert_equal(source.contains("val restore_after_queue = g_nvme.identify_namespace_id(previous_nsid)"), true)
assert_equal(source.contains("val restore_after_adapter = g_nvme.identify_namespace_id(previous_nsid)"), true)
assert_equal(source.contains("\"nvme-user-assign-namespace-restore-failed:\""), true)
assert_equal(source.contains("NvmeBlockAdapter.for_filesystem_lease(g_nvme, lease, consumer)"), true)
assert_equal(source.contains("val bounce = adapter.init_bounce_buffer()"), true)
assert_equal(source.contains("vfs_nvme_driver_instance_for_lease(name, adapter, lease, consumer)"), true)
assert_equal(source.contains("g_vfs_nvme_active_leases = g_vfs_nvme_active_leases.push(lease)"), true)
assert_equal(source.contains("g_vfs_nvme_direct_adapter_leases = g_vfs_nvme_direct_adapter_leases.push(lease)"), true)
assert_equal(source.contains("g_vfs_nvme_direct_adapters = g_vfs_nvme_direct_adapters.push(adapter)"), true)
assert_equal(lease_check_pos >= 0, true)
assert_equal(identify_pos > lease_check_pos, true)
assert_equal(queue_pos > lease_check_pos, true)
assert_equal(adapter_pos > lease_check_pos, true)
```

</details>

#### keeps direct IO adapter ownership mapped by lease instead of active lease index

- keeps direct IO adapter ownership mapped by lease instead of active lease index


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps direct IO adapter ownership mapped by lease instead of active lease index")
vfs_boot_nvme_reset_active_leases_for_test()
val grant = _tokenized_grant_for_owner(42u64)
val evidence = _user_evidence(grant)
val source = (read_file("src/os/services/vfs/vfs_boot_init.spl") + read_file("src/os/services/vfs/vfs_boot_core.spl") + read_file("src/os/services/vfs/vfs_boot_state.spl") + read_file("src/os/services/vfs/vfs_ambient_context.spl") + read_file("src/os/services/vfs/nvme_boot_runtime_owner.spl") + read_file("src/os/services/vfs/nvme_filesystem_direct_io.spl") + read_file("src/os/services/vfs/nvme_q35_lease_perf.spl") + read_file("src/os/services/vfs/direct_fat32_boot_reader.spl"))

val lease_only = vfs_boot_nvme_assign_user_namespace_lease(evidence, grant, 0u32, 16u32, 512u32, 65536u64, 0u64, 1024u64, SIMPLEOS_NVME_FIRST_DATA_QUEUE_ID, 42u64, 64u16, NvmeFilesystemConsumer.Nvfs)
assert_equal(lease_only.is_ok(), true)
assert_equal(vfs_boot_nvme_active_lease_count_for_test(), 1u64)
assert_equal(vfs_boot_nvme_direct_adapter_count_for_test(), 0u64)

assert_equal(source.contains("var g_vfs_nvme_direct_adapter_leases: [NvmeFilesystemLease] = []"), true)
assert_equal(source.contains("for adapter_lease in g_vfs_nvme_direct_adapter_leases:"), true)
assert_equal(source.contains("nvme_filesystem_lease_same_identity(active, lease)"), true)
assert_equal(source.contains("nvme_filesystem_lease_same_identity(adapter_lease, lease)"), true)
assert_equal(source.contains("var removed_direct_adapter = false"), true)
assert_equal(source.contains("removed_direct_adapter = true"), true)
assert_equal(source.contains("remaining_adapter_leases = remaining_adapter_leases.push(adapter_lease)"), true)
assert_equal(source.contains("g_vfs_nvme_direct_adapter_leases = remaining_adapter_leases"), true)
assert_equal(source.contains("g_nvme.release_user_data_queue_owner("), true)
assert_equal(source.contains("if lease.mode == NvmeNamespaceMode.UserAssigned and removed_direct_adapter:"), true)
assert_equal(source.contains("\"nvme-fs-user-queue-owner-release-failed\""), true)
assert_equal(source.contains("lease.queue.queue_id"), true)
assert_equal(source.contains("lease.queue.owner_task"), true)
assert_equal(source.contains("for active in g_vfs_nvme_active_leases:\n        if nvme_filesystem_lease_same_assignment(active, lease):\n            if idx >= g_vfs_nvme_direct_adapters.len():"), false)
vfs_boot_nvme_reset_active_leases_for_test()
```

</details>

#### requires filesystem DirectIo probe before submitting through lease adapters

- requires filesystem DirectIo probe before submitting through lease adapters


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires filesystem DirectIo probe before submitting through lease adapters")
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

assert_equal(vfs_boot_nvme_submit_filesystem_direct_4k(unsupported, lease, req).unwrap_err(), FsError.Unsupported)
assert_equal(vfs_boot_nvme_submit_filesystem_direct_4k(mounted, lease, unaligned).unwrap_err(), FsError.InvalidArg)
val mounted_batch = vfs_nvme_driver_instance_for_lease("user-dbfs", MemBlockDevice.new(1024u64, 512u32), lease, NvmeFilesystemConsumer.Dbfs).unwrap()
assert_equal(vfs_boot_nvme_submit_filesystem_direct_4k_batch(mounted_batch, lease, batch).unwrap_err(), FsError.NotFound)
vfs_boot_nvme_reset_active_leases_for_test()
```

</details>

#### resolves filesystem DirectIo through file extents before lease adapter submission

- resolves filesystem DirectIo through file extents before lease adapter submission


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves filesystem DirectIo through file extents before lease adapter submission")
val source = (read_file("src/os/services/vfs/vfs_boot_init.spl") + read_file("src/os/services/vfs/vfs_boot_core.spl") + read_file("src/os/services/vfs/vfs_boot_state.spl") + read_file("src/os/services/vfs/vfs_ambient_context.spl") + read_file("src/os/services/vfs/nvme_boot_runtime_owner.spl") + read_file("src/os/services/vfs/nvme_filesystem_direct_io.spl") + read_file("src/os/services/vfs/nvme_q35_lease_perf.spl") + read_file("src/os/services/vfs/direct_fat32_boot_reader.spl"))

assert_equal(source.contains("fn vfs_boot_nvme_map_filesystem_direct_4k_request(driver: DriverInstance, req: DirectIoRequest) -> Result<DirectIoRequest, FsError>:"), true)
assert_equal(source.contains("fn vfs_boot_nvme_map_filesystem_direct_4k_batch(driver: DriverInstance, req: DirectIoBatchRequest) -> Result<DirectIoBatchRequest, FsError>:"), true)
assert_equal(source.contains("driver.direct_io_extent_for_handle(FileHandle(id: req.handle_id), req.file_offset, 4096u64)"), true)
assert_equal(source.contains("val storage_offset = (mapped.storage_lba * mapped.sector_size.to_u64()) as i64"), true)
assert_equal(source.contains("file_offset: storage_offset"), true)
assert_equal(source.contains("for offset in req.file_offsets:\n        val extent = driver.direct_io_extent_for_handle(FileHandle(id: req.handle_id), offset, 4096u64)"), true)
assert_equal(source.contains("storage_offsets.push((mapped.storage_lba * mapped.sector_size.to_u64()) as i64)"), true)
assert_equal(source.contains("file_offsets: storage_offsets"), true)
assert_equal(source.contains("vfs_boot_nvme_direct_io_extent_matches_request(direct, mapped, req.file_offset, 4096u64)"), true)
assert_equal(source.contains("vfs_boot_nvme_direct_io_extent_matches_request(direct, mapped, offset, 4096u64)"), true)
```

</details>

#### rejects DirectIo extents that do not match the probed request

- rejects DirectIo extents that do not match the probed request


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects DirectIo extents that do not match the probed request")
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

assert_equal(vfs_boot_nvme_direct_io_extent_matches_request(dbfs, matching, 0i64, 4096u64), true)
assert_equal(vfs_boot_nvme_direct_io_extent_matches_request(dbfs, wrong_consumer, 0i64, 4096u64), false)
assert_equal(vfs_boot_nvme_direct_io_extent_matches_request(dbfs, missing_consumer, 0i64, 4096u64), false)
assert_equal(vfs_boot_nvme_direct_io_extent_matches_request(dbfs, wrong_offset, 0i64, 4096u64), false)
assert_equal(vfs_boot_nvme_direct_io_extent_matches_request(dbfs, wrong_len, 0i64, 4096u64), false)
```

</details>

#### exposes boot FAT DirectIo extents on the pure SimpleOS shared FAT driver

- exposes boot FAT DirectIo extents on the pure SimpleOS shared FAT driver


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exposes boot FAT DirectIo extents on the pure SimpleOS shared FAT driver")
val source = read_file("src/os/services/fat32/shared_fat32_driver.spl")

assert_equal(source.contains("use std.fs_driver.direct_io.{DirectIoExtent}"), true)
assert_equal(source.contains("me fn direct_io_extent_for_handle(handle: u64, file_offset: i64, byte_len: u64) -> Result<DirectIoExtent, text>:"), true)
assert_equal(source.contains("return Result.Err(\"invalid file handle\")"), true)
assert_equal(source.contains("self.inner.direct_io_extent_for_handle(shared_opt.unwrap(), file_offset, byte_len)"), true)
```

</details>

#### rejects uncommitted DBFS filesystem DirectIo batches before adapter lookup

- rejects uncommitted DBFS filesystem DirectIo batches before adapter lookup


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects uncommitted DBFS filesystem DirectIo batches before adapter lookup")
val lease = _user_lease_for_boot_nsid(19u32)
val mounted = vfs_nvme_driver_instance_for_lease("user-dbfs", MemBlockDevice.new(1024u64, 512u32), lease, NvmeFilesystemConsumer.Dbfs).unwrap()
val handle = mounted.open_path(Path(raw: "/hot.db"), OpenFlags.read_write().with_create())
assert_equal(handle.is_ok(), true)
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
assert_equal(mapped.unwrap_err(), FsError.Unsupported)
```

</details>

#### rejects uncommitted NVFS filesystem DirectIo before adapter lookup

- rejects uncommitted NVFS filesystem DirectIo before adapter lookup


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects uncommitted NVFS filesystem DirectIo before adapter lookup")
val lease = _user_lease_for_boot_nsid(20u32)
val mounted = vfs_nvme_driver_instance_for_lease("user-nvfs", MemBlockDevice.new(1024u64, 512u32), lease, NvmeFilesystemConsumer.Nvfs).unwrap()
val handle = mounted.open_path(Path(raw: "/hot.nvfs"), OpenFlags.read_write().with_create())
assert_equal(handle.is_ok(), true)
val single = direct_io_read_request(handle.unwrap().id, 4096i64, _valid_shared_dma_4k(), 100u32)
val mapped = vfs_boot_nvme_map_filesystem_direct_4k_request(mounted, single)
assert_equal(mapped.unwrap_err(), FsError.Unsupported)
```

</details>

#### wires q35 pure Simple perf evidence to real shared-DMA direct I/O

- wires q35 pure Simple perf evidence to real shared-DMA direct I/O


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wires q35 pure Simple perf evidence to real shared-DMA direct I/O")
val source = (read_file("src/os/services/vfs/vfs_boot_init.spl") + read_file("src/os/services/vfs/vfs_boot_core.spl") + read_file("src/os/services/vfs/vfs_boot_state.spl") + read_file("src/os/services/vfs/vfs_ambient_context.spl") + read_file("src/os/services/vfs/nvme_boot_runtime_owner.spl") + read_file("src/os/services/vfs/nvme_filesystem_direct_io.spl") + read_file("src/os/services/vfs/nvme_q35_lease_perf.spl") + read_file("src/os/services/vfs/direct_fat32_boot_reader.spl"))
val entry = read_file("examples/09_embedded/simple_os/arch/x86_64/q35_pure_nvme_perf_entry.spl")

assert_equal(source.contains("fn vfs_boot_nvme_q35_pure_simple_perf_probe_serial_lines() -> [text]:"), true)
assert_equal(source.contains("val batch_4k_ops: u32 = 32u32"), true)
assert_equal(source.contains("dma_alloc(batch_bytes as i64, DmaDir.Bidirectional)"), true)
assert_equal(source.contains("vfs_boot_nvme_submit_active_lease_direct_4k_batch("), true)
assert_equal(source.contains("direct_io_read_batch_request(1u64, offsets, shared, 100000u32)"), true)
assert_equal(source.contains("direct_io_write_batch_request(1u64, offsets, shared, 100000u32)"), true)
assert_equal(source.contains("vfs_boot_nvme_submit_active_lease_direct_4k_batch_write_through("), true)
assert_equal(source.contains("fn _vfs_boot_q35_ready_fs_consumers(lease: NvmeFilesystemLease) -> Result<text, text>:"), true)
assert_equal(source.contains("vfs_boot_nvme_shared_consumer_interface_reason(lease)"), true)
assert_equal(source.contains("nvme_filesystem_lease_reason(lease, NvmeFilesystemConsumer.Fat32)"), true)
assert_equal(source.contains("nvme_filesystem_lease_reason(lease, NvmeFilesystemConsumer.Nvfs)"), true)
assert_equal(source.contains("nvme_filesystem_lease_reason(lease, NvmeFilesystemConsumer.Dbfs)"), true)
assert_equal(source.contains("fs-consumer-lease-not-ready"), true)
assert_equal(source.contains("/SYS/PERF/CFAT4K.TXT"), true)
assert_equal(source.contains("real_device_q35_pure_simple_perf_marker_from_measurements("), true)
assert_equal(source.contains("reason=c-baseline-missing-iops"), true)
assert_equal(entry.contains("q35_pure_nvme_perf_serial_lines"), true)
assert_equal(entry.contains("serial_println(line)"), true)
val pcimgr = read_file("src/os/services/pcimgr/pcimgr.spl")
assert_equal(pcimgr.contains("fn pcimgr_enable_mmio_bus_master"), true)
assert_equal(pcimgr.contains("command | 0x00000006u32"), true)
assert_equal(pcimgr.contains("pcimgr_enable_mmio_bus_master(bus_u8, dev_u8, func_u8)"), true)
```

</details>

#### measures the standalone q35 C baseline inside the guest on the same device

- measures the standalone q35 C baseline inside the guest on the same device


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("measures the standalone q35 C baseline inside the guest on the same device")
val source = read_file("src/os/services/vfs/q35_pure_nvme_perf_boot.spl")

assert_equal(source.contains("extern fn simpleos_nvme_init() -> i64"), true)
assert_equal(source.contains("extern fn simpleos_nvme_read_sector(device_idx: u64, lba: u64, buf_addr: u64) -> i64"), true)
assert_equal(source.contains("extern fn simpleos_nvme_write_sector(device_idx: u64, lba: u64, buf_addr: u64) -> i64"), true)
assert_equal(source.contains("fn _measure_c_bridge_4k_baseline(lbas: [u64], sector_size: u32, buf_addr: u64) -> Result<Q35NvmePerfCounters, text>:"), true)
assert_equal(source.contains("val init = simpleos_nvme_init()"), true)
assert_equal(source.contains("simpleos_nvme_read_sector(0u64, lba + sector.to_u64(), buf_addr"), true)
assert_equal(source.contains("simpleos_nvme_write_sector(0u64, lba + sector.to_u64(), buf_addr"), true)
assert_equal(source.contains("all_lbas.push(lba)"), true)
assert_equal(source.contains("val c_baseline = _measure_c_bridge_4k_baseline(all_lbas, sector_size, shared.cpu_virt_addr)"), true)
assert_equal(source.contains("c_read_iops = c.read_iops"), true)
assert_equal(source.contains("c_write_iops = c.write_iops"), true)
assert_equal(source.contains("if read_p99_us >= c_read_p99_us:"), true)
assert_equal(source.contains("simple-read-p99-not-faster-than-c"), true)
assert_equal(source.contains("if write_p99_us >= c_write_p99_us:"), true)
assert_equal(source.contains("simple-write-p99-not-faster-than-c"), true)
```

</details>

#### measures standalone q35 Simple I/O through the lease-backed adapter DirectIo surface

- measures standalone q35 Simple I/O through the lease-backed adapter DirectIo surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 59 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("measures standalone q35 Simple I/O through the lease-backed adapter DirectIo surface")
val source = read_file("src/os/services/vfs/q35_pure_nvme_perf_boot.spl")

assert_equal(source.contains("use os.services.vfs.vfs_block_adapters.{NvmeBlockAdapter}"), true)
assert_equal(source.contains("nvme_transfer_readiness_reason(evidence)"), true)
assert_equal(source.contains("NvmeBlockAdapter.submit_direct_4k_shared_dma_batch_for_lease_window(nvme, 1u32, SIMPLEOS_NVME_SYSTEM_QUEUE_ID, consumer, 0u64, sector_count, sector_size, read_req)"), true)
assert_equal(source.contains("NvmeBlockAdapter.submit_direct_4k_shared_dma_batch_write_through_for_lease_window(nvme, 1u32, SIMPLEOS_NVME_SYSTEM_QUEUE_ID, consumer, 0u64, sector_count, sector_size, write_req)"), true)
assert_equal(source.contains("NvmeBlockAdapter.submit_direct_4k_shared_dma_batch_for_identified_namespace"), false)
val adapter = read_file("src/os/services/vfs/vfs_block_adapters.spl")
assert_equal(adapter.contains("static fn submit_direct_4k_shared_dma_batch_for_lease("), true)
assert_equal(adapter.contains("static fn submit_direct_4k_shared_dma_batch_for_lease_window("), true)
assert_equal(adapter.contains("static fn submit_direct_4k_shared_dma_batch_write_through_for_lease("), true)
assert_equal(adapter.contains("static fn submit_direct_4k_shared_dma_batch_write_through_for_lease_window("), true)
assert_equal(adapter.contains("nvme.flush_in_namespace_on_queue(lease.namespace_identity.nsid, lease.queue.queue_id)"), true)
assert_equal(adapter.contains("nvme.flush_in_namespace_on_queue(nsid, queue_id)"), true)
assert_equal(adapter.contains("durable: true"), true)
assert_equal(adapter.contains("durable: false"), true)
assert_equal(adapter.contains("lease: NvmeFilesystemLease"), true)
assert_equal(adapter.contains("val reason = nvme_filesystem_lease_reason(lease, consumer)"), true)
assert_equal(adapter.contains("nvme_filesystem_lease_absolute_lba(lease, relative_lba)"), true)
assert_equal(adapter.contains("if relative_lba >= lba_count:"), true)
assert_equal(adapter.contains("direct_io_validate_batch(ext, req, 4096u64)"), true)
assert_equal(source.contains("fn _fat32_fixture_direct_offsets(nvme: NvmeDriver, sector_size: u32, buf: SharedDmaBuffer) -> Result<[i64], text>:"), true)
assert_equal(source.contains("\"FAT4K   BIN\""), true)
assert_equal(source.contains("fat32_extent_source=freestanding-fat32-extents"), true)
assert_equal(source.contains("fn _dbfs_arena_direct_offsets(sector_size: u32, sector_count: u64, arena_base_lba: u64) -> Result<[i64], text>:"), true)
assert_equal(source.contains("nvfs_extent_source=freestanding-dbfs-arena"), true)
assert_equal(source.contains("dbfs_extent_source=freestanding-dbfs-arena"), true)
assert_equal(source.contains("fat32_direct_io=read-write-through"), true)
assert_equal(source.contains("nvfs_direct_io=read-write-through"), true)
assert_equal(source.contains("dbfs_direct_io=read-write-through"), true)
assert_equal(source.contains("fn _consumer_for_measurement(run: u32, op: u32) -> NvmeFilesystemConsumer:"), true)
assert_equal(source.contains("saw_fat32 = true"), true)
assert_equal(source.contains("saw_nvfs = true"), true)
assert_equal(source.contains("saw_dbfs = true"), true)
assert_equal(source.contains("fs-consumer-direct-io-incomplete"), true)
assert_equal(source.contains("fs_consumers=\" + fs_consumers"), true)
assert_equal(source.contains("direct_io_read_batch_request(1u64, offsets, shared, 200000u32)"), true)
assert_equal(source.contains("direct_io_write_batch_request(1u64, offsets, shared, 200000u32)"), true)
assert_equal(source.contains("fn _q35_user_namespace_assignment_marker("), true)
assert_equal(source.contains("active_leases: [NvmeFilesystemLease]"), true)
assert_equal(source.contains("val active_system_lease = _q35_system_namespace_lease(sector_size, sector_count)"), true)
assert_equal(source.contains("val system_nsid = 1u32"), true)
assert_equal(source.contains("val user_namespace = nvme.identify_first_assignable_user_namespace(system_nsid)"), true)
assert_equal(source.contains("val user_nsid = user_facts.nsid"), true)
assert_equal(source.contains("nvme_user_assigned_filesystem_lease_from_grant_checked(\n        evidence,\n        grant,\n        0u32,\n        1u32,"), false)
assert_equal(source.contains("nvme_user_assigned_filesystem_lease_from_grant_checked(\n        evidence,\n        grant,\n        0u32,\n        user_nsid,"), true)
assert_equal(source.contains("_q35_user_namespace_assignment_marker(nvme, grant, shared, [active_system_lease])"), true)
assert_equal(source.contains("NvmeFilesystemConsumer.Fat32,\n        []"), false)
assert_equal(source.contains("user_namespace_assignment=hardware-data-queue"), true)
assert_equal(source.contains("user_namespace_nsid=\" + lease.namespace_identity.nsid.to_u64().to_text()"), true)
assert_equal(source.contains("user_namespace_active_lease_count=\" + active_leases.len().to_u64().to_text()"), true)
assert_equal(source.contains("user_namespace_direct_io=read-write-through"), true)
assert_equal(source.contains("nvme_shared_filesystem_interface(lease)"), true)
assert_equal(source.contains("user_namespace_shared_interface=\" + nvme_shared_filesystem_interface_consumers()"), true)
assert_equal(source.contains("NvmeBlockAdapter.submit_direct_4k_shared_dma_batch_write_through_for_lease("), true)
assert_equal(source.contains("nvme.read_4k_shared_dma_batch_in_namespace_on_queue("), false)
assert_equal(source.contains("nvme.write_4k_shared_dma_batch_in_namespace_on_queue("), false)
```

</details>

#### packages the C FAT baseline artifact into the q35 FAT image contract

- packages the C FAT baseline artifact into the q35 FAT image contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("packages the C FAT baseline artifact into the q35 FAT image contract")
val script = read_file("scripts/os/make_os_disk.shs")
assert_equal(script.contains("SIMPLEOS_CFAT4K_BASELINE"), true)
assert_equal(script.contains("build\", \"os\", \"perf\", \"CFAT4K.TXT"), true)
assert_equal(script.contains("sys_entries.append(dir_entry(\"PERF       \""), true)
assert_equal(script.contains("perf_entries.append(dir_entry(\"CFAT4K  TXT\""), true)
assert_equal(script.contains("SIMPLEOS_FAT32_DIRECT_IO_4K_FIXTURE"), true)
assert_equal(script.contains("perf_entries.append(dir_entry(\"FAT4K   BIN\""), true)
assert_equal(script.contains("spc = 8"), true)
```

</details>

#### checks shared driver readiness before constructing hardware user namespace adapters

- checks shared driver readiness before constructing hardware user namespace adapters


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks shared driver readiness before constructing hardware user namespace adapters")
vfs_boot_nvme_reset_active_leases_for_test()
val source = (read_file("src/os/services/vfs/vfs_boot_init.spl") + read_file("src/os/services/vfs/vfs_boot_core.spl") + read_file("src/os/services/vfs/vfs_boot_state.spl") + read_file("src/os/services/vfs/vfs_ambient_context.spl") + read_file("src/os/services/vfs/nvme_boot_runtime_owner.spl") + read_file("src/os/services/vfs/nvme_filesystem_direct_io.spl") + read_file("src/os/services/vfs/nvme_q35_lease_perf.spl") + read_file("src/os/services/vfs/direct_fat32_boot_reader.spl"))
val guard_pos = source.index_of("val driver_ready = vfs_boot_nvme_shared_driver_ready_for_user_assignment()")
val adapter_pos = source.index_of("NvmeBlockAdapter.for_filesystem_lease(g_nvme, lease, consumer)")

assert_equal(vfs_boot_nvme_shared_driver_ready_for_user_assignment(), "nvme-user-assign-boot-storage-not-ready:not-mounted")
assert_equal(guard_pos >= 0, true)
assert_equal(adapter_pos > guard_pos, true)
assert_equal(vfs_boot_nvme_active_lease_count_for_test(), 0u64)
```

</details>

#### releases user data queue owners on post-queue hardware assignment failures

- releases user data queue owners on post-queue hardware assignment failures


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("releases user data queue owners on post-queue hardware assignment failures")
val source = (read_file("src/os/services/vfs/vfs_boot_init.spl") + read_file("src/os/services/vfs/vfs_boot_core.spl") + read_file("src/os/services/vfs/vfs_boot_state.spl") + read_file("src/os/services/vfs/vfs_ambient_context.spl") + read_file("src/os/services/vfs/nvme_boot_runtime_owner.spl") + read_file("src/os/services/vfs/nvme_filesystem_direct_io.spl") + read_file("src/os/services/vfs/nvme_q35_lease_perf.spl") + read_file("src/os/services/vfs/direct_fat32_boot_reader.spl"))
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

assert_equal(helper_pos >= 0, true)
assert_equal(fn_start >= 0, true)
assert_equal(fn_end > fn_start, true)
assert_equal(source.contains("g_nvme.release_user_data_queue_owner(\n        lease.queue.queue_id,\n        lease.namespace_identity.controller_id,\n        lease.namespace_identity.nsid,\n        lease.queue.owner_task\n    )"), true)
assert_equal(adapter_fail_pos > queue_pos, true)
assert_equal(bounce_fail_pos > queue_pos, true)
assert_equal(driver_fail_pos > queue_pos, true)
assert_equal(adapter_fail_pos < record_pos, true)
assert_equal(bounce_fail_pos < record_pos, true)
assert_equal(driver_fail_pos < record_pos, true)
assert_equal(adapter_fail_body.index_of("val restore_after_adapter = g_nvme.identify_namespace_id(previous_nsid)") < adapter_fail_body.index_of("val queue_release = vfs_boot_nvme_release_user_queue_owner_for_failed_assignment(lease)"), true)
assert_equal(adapter_fail_body.contains("vfs_boot_nvme_release_user_queue_owner_for_failed_assignment(lease)"), true)
assert_equal(bounce_fail_body.contains("vfs_boot_nvme_release_user_queue_owner_for_failed_assignment(lease)"), true)
assert_equal(driver_fail_body.contains("vfs_boot_nvme_release_user_queue_owner_for_failed_assignment(lease)"), true)
```

</details>

#### releases active user namespace leases so reassignment can proceed

- releases active user namespace leases so reassignment can proceed


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("releases active user namespace leases so reassignment can proceed")
vfs_boot_nvme_reset_active_leases_for_test()
val grant = _tokenized_grant_for_owner(42u64)
val evidence = _user_evidence(grant)
val assigned = vfs_boot_nvme_assign_user_namespace_lease(evidence, grant, 0u32, 14u32, 512u32, 65536u64, 0u64, 1024u64, SIMPLEOS_NVME_FIRST_DATA_QUEUE_ID, 42u64, 64u16, NvmeFilesystemConsumer.Nvfs).unwrap()
val missing = _user_lease_for_boot_nsid(15u32)

assert_equal(vfs_boot_nvme_active_lease_count_for_test(), 1u64)
assert_equal(vfs_boot_nvme_release_active_lease(missing), "nvme-fs-active-lease-not-found")
assert_equal(vfs_boot_nvme_active_lease_count_for_test(), 1u64)
assert_equal(vfs_boot_nvme_release_active_lease(assigned), "ready")
assert_equal(vfs_boot_nvme_active_lease_count_for_test(), 0u64)
val reassigned = vfs_boot_nvme_assign_user_namespace_lease(evidence, grant, 0u32, 14u32, 512u32, 65536u64, 0u64, 1024u64, SIMPLEOS_NVME_FIRST_DATA_QUEUE_ID, 42u64, 64u16, NvmeFilesystemConsumer.Nvfs)
assert_equal(reassigned.is_ok(), true)
assert_equal(vfs_boot_nvme_active_lease_count_for_test(), 1u64)
vfs_boot_nvme_reset_active_leases_for_test()
```

</details>

#### accepts only pure Simple NVMe boot storage as production-ready

- accepts only pure Simple NVMe boot storage as production-ready


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts only pure Simple NVMe boot storage as production-ready")
assert_equal(vfs_boot_storage_acceptance_reason(false, "not-mounted", false), "not-mounted")
assert_equal(vfs_boot_storage_acceptance_reason(true, "c-boot-bridge", false), "vfs-boot-storage-not-pure-simple:c-boot-bridge")
assert_equal(vfs_boot_storage_acceptance_reason(true, "virtio-blk", true), "vfs-boot-storage-not-nvme-simple-driver:virtio-blk")
assert_equal(vfs_boot_storage_acceptance_reason(true, "simple-driver", true), "ready")
assert_equal(vfs_boot_storage_production_ready(true, "c-boot-bridge", false), false)
assert_equal(vfs_boot_storage_production_ready(true, "virtio-blk", true), false)
assert_equal(vfs_boot_storage_production_ready(true, "simple-driver", true), true)
```

</details>

#### keeps production VFS boot out of C bridge and virtio fallback branches

- keeps production VFS boot out of C bridge and virtio fallback branches


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps production VFS boot out of C bridge and virtio fallback branches")
val source = (read_file("src/os/services/vfs/vfs_boot_init.spl") + read_file("src/os/services/vfs/vfs_boot_core.spl") + read_file("src/os/services/vfs/vfs_boot_state.spl") + read_file("src/os/services/vfs/vfs_ambient_context.spl") + read_file("src/os/services/vfs/nvme_boot_runtime_owner.spl") + read_file("src/os/services/vfs/nvme_filesystem_direct_io.spl") + read_file("src/os/services/vfs/nvme_q35_lease_perf.spl") + read_file("src/os/services/vfs/direct_fat32_boot_reader.spl"))
val boot_pos = source.index_of("pub fn vfs_boot_init() -> bool:")
val production_pos = source.index_of("pub fn vfs_boot_init_production() -> bool:")
val pure_pos = source.index_of("fn _vfs_boot_init_pure_nvme_fat32")
val boot_body = source.substring(boot_pos, production_pos)
val production_body = source.substring(production_pos, pure_pos)

assert_equal(boot_body.contains("init_c_bridge()"), false)
assert_equal(boot_body.contains("_vfs_boot_init_virtio_fat32()"), false)
assert_equal(boot_body.contains("pure-Simple NVMe + FAT32 unavailable; VFS unavailable"), true)
assert_equal(production_body.contains("vfs_boot_init()"), false)
assert_equal(production_body.contains("init_c_bridge()"), false)
assert_equal(production_body.contains("_vfs_boot_init_virtio_fat32()"), false)
assert_equal(production_body.contains("_vfs_boot_init_pure_nvme_fat32(nvme_idx.to_u64())"), true)
```

</details>

#### exports fail-closed production readiness through the VFS public surface

- exports fail-closed production readiness through the VFS public surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exports fail-closed production readiness through the VFS public surface")
assert_equal(vfs_boot_storage_acceptance_ready(), false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/services/vfs/vfs_boot_nvme_lease_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering VFS boot NVMe lease contract.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `56f68d4514d30da792793cf53fe21f01ec9dbdccbd259aa6ea70d94e596b7115`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `56f68d4514d30da792793cf53fe21f01ec9dbdccbd259aa6ea70d94e596b7115`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `56f68d4514d30da792793cf53fe21f01ec9dbdccbd259aa6ea70d94e596b7115`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/unit/os/services/vfs/vfs_boot_nvme_lease_spec.spl
mirror: doc/06_spec/unit/os/services/vfs/vfs_boot_nvme_lease_spec.md (current)
findings: 6 blockers: 0
  narrative=80 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/services/vfs/vfs_boot_nvme_lease_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/services/vfs/vfs_boot_nvme_lease_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/services/vfs/vfs_boot_nvme_lease_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/unit/os/services/vfs/vfs_boot_nvme_lease_spec.spl:116:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds a filesystem-ready system FAT32 lease for pure Simple boot' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/services/vfs/vfs_boot_nvme_lease_spec.spl:127:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps invalid namespace geometry rejected before FAT32 can mount' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/services/vfs/vfs_boot_nvme_lease_spec.spl:191:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records boot NVMe leases and rejects later user assignment of the same namespace' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
