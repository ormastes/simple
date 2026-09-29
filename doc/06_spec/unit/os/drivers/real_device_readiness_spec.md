# Real Device Readiness Specification

> Tests covering SimpleOS real-device readiness.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Real Device Readiness Specification

## Scenarios

### SimpleOS real-device readiness

#### accepts q35 NVMe and virtio-net only with hardware evidence

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts q35 NVMe and virtio-net only with hardware evidence
   - Expected: real_device_readiness_ready(ready) is true
   - Expected: real_device_readiness_reason(ready) equals `ready`
   - Expected: cmd[0] equals `qemu-system-x86_64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts q35 NVMe and virtio-net only with hardware evidence")
val ready = real_device_readiness_with_providers(
    "x86_64-q35",
    "q35-config-io",
    true,
    "nvme",
    true,
    true,
    "virtio-net",
    true,
    true,
    "off",
    false,
    true,
    true,
    "simple-driver",
    "simple-driver",
    "none"
)
expect(real_device_readiness_ready(ready)).to_equal(true)
expect(real_device_readiness_reason(ready)).to_equal("ready")
expect(real_device_marker(ready)).to_contain("storage=nvme")
expect(real_device_marker(ready)).to_contain("network=virtio-net")

val args = real_device_qemu_args(ready)
expect(args).to_contain("nvme,drive=nvme0,serial=simpleos0")
expect(args).to_contain("virtio-net-pci,netdev=net0")

val custom_args = real_device_qemu_args_for_image(ready, "build/os/q35-nvme.img")
expect(custom_args).to_contain("file=build/os/q35-nvme.img,if=none,id=nvme0,format=raw")

val cmd = real_device_q35_qemu_command(ready, "build/os/simpleos_x86_64.elf", "build/os/q35-nvme.img")
expect(cmd[0]).to_equal("qemu-system-x86_64")
expect(cmd).to_contain("-machine")
expect(cmd).to_contain("q35")
expect(cmd).to_contain("-kernel")
expect(cmd).to_contain("build/os/simpleos_x86_64.elf")
expect(cmd).to_contain("file=build/os/q35-nvme.img,if=none,id=nvme0,format=raw")
expect(cmd).to_contain("virtio-net-pci,netdev=net0")
```

</details>

#### rejects fallback or incomplete storage and network claims

- rejects fallback or incomplete storage and network claims
   - Expected: real_device_readiness_ready(no_pci_board) is false
   - Expected: real_device_readiness_reason(no_pci_board) equals `missing-pci-board:mps2-an505`
   - Expected: real_device_q35_qemu_command(no_pci_board, "kernel.elf", "disk.img").len() equals `0`
   - Expected: real_device_readiness_reason(no_identify) equals `missing-nvme-identify`
   - Expected: real_device_readiness_reason(no_rx_tx) equals `missing-network-rx-tx:e1000`
   - Expected: real_device_readiness_ready(unspecified_provider) is false
   - Expected: real_device_readiness_reason(unspecified_provider) equals `storage-provider-not-hardware:unspecified`


<details>
<summary>Executable SSpec</summary>

Runnable source: 76 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects fallback or incomplete storage and network claims")
val no_pci_board = real_device_readiness(
    "mps2-an505",
    "none",
    false,
    "nvme",
    true,
    true,
    "off",
    false,
    false,
    "off",
    false,
    true,
    false
)
val no_identify = real_device_readiness_with_providers(
    "x86_64-q35",
    "q35-config-io",
    true,
    "nvme",
    false,
    true,
    "off",
    false,
    false,
    "off",
    false,
    true,
    true,
    "simple-driver",
    "none",
    "none"
)
val no_rx_tx = real_device_readiness_with_providers(
    "x86_64-q35",
    "q35-config-io",
    true,
    "off",
    false,
    false,
    "e1000",
    true,
    false,
    "off",
    false,
    true,
    true,
    "none",
    "simple-driver",
    "none"
)
val unspecified_provider = real_device_readiness(
    "x86_64-q35",
    "q35-config-io",
    true,
    "nvme",
    true,
    true,
    "virtio-net",
    true,
    true,
    "off",
    false,
    true,
    true
)

expect(real_device_readiness_ready(no_pci_board)).to_equal(false)
expect(real_device_readiness_reason(no_pci_board)).to_equal("missing-pci-board:mps2-an505")
expect(real_device_q35_qemu_command(no_pci_board, "kernel.elf", "disk.img").len()).to_equal(0)
expect(real_device_readiness_reason(no_identify)).to_equal("missing-nvme-identify")
expect(real_device_readiness_reason(no_rx_tx)).to_equal("missing-network-rx-tx:e1000")
expect(real_device_readiness_ready(unspecified_provider)).to_equal(false)
expect(real_device_readiness_reason(unspecified_provider)).to_equal("storage-provider-not-hardware:unspecified")
```

</details>

#### distinguishes current C bridge evidence from pure Simple driver completion

- distinguishes current C bridge evidence from pure Simple driver completion
   - Expected: real_device_readiness_ready(current) is false
   - Expected: real_device_readiness_reason(current) equals `storage-provider-not-hardware:c-boot-bridge`
   - Expected: real_device_pure_simple_ready(current) is false
   - Expected: real_device_pure_simple_reason(current) equals `storage-not-pure-simple:c-boot-bridge`
   - Expected: real_device_readiness_ready(pure) is true
   - Expected: real_device_pure_simple_ready(pure) is false
   - Expected: real_device_pure_simple_reason(pure) equals `storage-direct-access:missing-required-access:mmio:direct-access-not-user-spa... (full value in folded executable source)`
   - Expected: real_device_pure_simple_ready(pure_with_access) is true
   - Expected: real_device_pure_simple_reason(pure_with_access) equals `ready`
   - Expected: real_device_direct_access_reason(pure_with_access) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 65 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("distinguishes current C bridge evidence from pure Simple driver completion")
val current = real_device_current_q35_c_bridge_readiness()
expect(real_device_readiness_ready(current)).to_equal(false)
expect(real_device_readiness_reason(current)).to_equal("storage-provider-not-hardware:c-boot-bridge")
expect(real_device_pure_simple_ready(current)).to_equal(false)
expect(real_device_pure_simple_reason(current)).to_equal("storage-not-pure-simple:c-boot-bridge")
expect(real_device_marker(current)).to_contain("storage_provider=c-boot-bridge")
expect(real_device_marker(current)).to_contain("network_provider=c-boot-bridge")

val pure = real_device_readiness_with_providers(
    "x86_64-q35",
    "q35-config-io",
    true,
    "nvme",
    true,
    true,
    "virtio-net",
    true,
    true,
    "off",
    false,
    true,
    true,
    "simple-driver",
    "simple-driver",
    "none"
)
expect(real_device_readiness_ready(pure)).to_equal(true)
expect(real_device_pure_simple_ready(pure)).to_equal(false)
expect(real_device_pure_simple_reason(pure)).to_equal("storage-direct-access:missing-required-access:mmio:direct-access-not-user-space-driver:unknown")

val pure_with_access = real_device_readiness_with_access(
    "x86_64-q35",
    "q35-config-io",
    true,
    "nvme",
    true,
    true,
    "virtio-net",
    true,
    true,
    "off",
    false,
    true,
    true,
    "simple-driver",
    "simple-driver",
    "none",
    "user-space-driver",
    "raw-device-grant:tok=101",
    "non-secure-resource-namespace",
    true,
    "user-space-driver",
    "resource-grant-set:tok=202",
    "non-secure-resource-namespace",
    true,
    "unknown",
    "none",
    "none",
    false
)
expect(real_device_pure_simple_ready(pure_with_access)).to_equal(true)
expect(real_device_pure_simple_reason(pure_with_access)).to_equal("ready")
expect(real_device_direct_access_reason(pure_with_access)).to_equal("ready")
```

</details>

#### lists q35 boot markers needed for real storage and network acceptance

- lists q35 boot markers needed for real storage and network acceptance


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists q35 boot markers needed for real storage and network acceptance")
val markers = real_device_q35_boot_markers()
expect(markers).to_contain("[stage1] nvme_identify_read=pass")
expect(markers).to_contain("[stage1] nvme_rw_restore=pass")
expect(markers).to_contain("[stage1] virtio_net_tx_rx=pass")
expect(markers).to_contain("TEST PASSED")
```

</details>

#### requires provider and direct-access serial markers for pure q35 completion

- requires provider and direct-access serial markers for pure q35 completion
   - Expected: real_device_q35_pure_simple_serial_accepts_completion(c_bridge_serial) is false
   - Expected: real_device_q35_pure_simple_serial_acceptance_reason(c_bridge_serial) equals `storage-not-pure-simple:c-boot-bridge`
   - Expected: real_device_q35_pure_simple_serial_acceptance_reason(missing_access) equals `missing-pure-simple-marker:storage_placement=user-space-driver`
   - Expected: real_device_q35_pure_simple_serial_accepts_completion(tokenless_grants) is false
   - Expected: real_device_q35_pure_simple_serial_acceptance_reason(tokenless_grants) equals `missing-pure-simple-marker:storage_grant=resource-grant-set:tok=`
   - Expected: real_device_q35_pure_simple_serial_accepts_completion(missing_perf) is false
   - Expected: real_device_q35_pure_simple_serial_acceptance_reason(missing_perf) equals `missing-pure-simple-marker:nvme_perf reason=ready`
   - Expected: real_device_q35_pure_simple_serial_accepts_completion(ready_serial) is true
   - Expected: real_device_q35_pure_simple_serial_acceptance_reason(ready_serial) equals `ready`
   - Expected: real_device_q35_pure_simple_serial_acceptance_reason(spoofed_placement) equals `missing-pure-simple-marker:storage_placement=user-space-driver`
   - Expected: real_device_q35_pure_simple_serial_acceptance_reason(spoofed_grant) equals `missing-pure-simple-marker:storage_grant=resource-grant-set:tok=`


<details>
<summary>Executable SSpec</summary>

Runnable source: 80 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires provider and direct-access serial markers for pure q35 completion")
val c_bridge_serial =
    "[stage1] pci_count=7\n" +
    "[stage1] nvme_pci=present\n" +
    "[stage1] nvme_identify_read=pass\n" +
    "[stage1] nvme_rw_restore=pass\n" +
    "[stage1] net_pci=present\n" +
    "[stage1] virtio_net_tx_rx=pass\n" +
    "[real-device] storage_provider=c-boot-bridge network_provider=c-boot-bridge\n" +
    "TEST PASSED\n"
expect(real_device_q35_pure_simple_serial_accepts_completion(c_bridge_serial)).to_equal(false)
expect(real_device_q35_pure_simple_serial_acceptance_reason(c_bridge_serial)).to_equal("storage-not-pure-simple:c-boot-bridge")

val missing_access =
    "[stage1] pci_count=7\n" +
    "[stage1] nvme_pci=present\n" +
    "[stage1] nvme_identify_read=pass\n" +
    "[stage1] nvme_rw_restore=pass\n" +
    "[stage1] net_pci=present\n" +
    "[stage1] virtio_net_tx_rx=pass\n" +
    "[real-device] storage_provider=simple-driver network_provider=simple-driver\n" +
    "TEST PASSED\n"
expect(real_device_q35_pure_simple_serial_acceptance_reason(missing_access)).to_equal("missing-pure-simple-marker:storage_placement=user-space-driver")

val tokenless_grants =
    "[stage1] pci_count=7\n" +
    "[stage1] nvme_pci=present\n" +
    "[stage1] nvme_identify_read=pass\n" +
    "[stage1] nvme_rw_restore=pass\n" +
    "[stage1] net_pci=present\n" +
    "[stage1] virtio_net_tx_rx=pass\n" +
    "[real-device] storage_provider=simple-driver network_provider=simple-driver " +
    "storage_placement=user-space-driver system_storage_placement=system-driver network_placement=user-space-driver " +
    "storage_namespace=non-secure-resource-namespace network_namespace=non-secure-resource-namespace " +
    "storage_grant=resource-grant-set network_grant=resource-grant-set common_driver_logic=shared\n" +
    "TEST PASSED\n"
expect(real_device_q35_pure_simple_serial_accepts_completion(tokenless_grants)).to_equal(false)
expect(real_device_q35_pure_simple_serial_acceptance_reason(tokenless_grants)).to_equal("missing-pure-simple-marker:storage_grant=resource-grant-set:tok=")

val missing_perf =
    "[stage1] pci_count=7\n" +
    "[stage1] nvme_pci=present\n" +
    "[stage1] nvme_identify_read=pass\n" +
    "[stage1] nvme_rw_restore=pass\n" +
    "[stage1] net_pci=present\n" +
    "[stage1] virtio_net_tx_rx=pass\n" +
    "[real-device] storage_provider=simple-driver network_provider=simple-driver " +
    "storage_placement=user-space-driver system_storage_placement=system-driver network_placement=user-space-driver " +
    "storage_namespace=non-secure-resource-namespace network_namespace=non-secure-resource-namespace " +
    "storage_grant=resource-grant-set:tok=101 network_grant=resource-grant-set:tok=202 common_driver_logic=shared\n" +
    "TEST PASSED\n"
val ready_serial = missing_perf +
    "nvme_perf reason=ready simple_provider=simple-driver " +
    "workload=4k-random-read-write io_size_bytes=4096 " +
    "direct_io_path=nvme-lease-shared-dma-4k fs_consumers=fat32,nvfs,dbfs fat32_direct_io=read-write-through nvfs_direct_io=read-write-through dbfs_direct_io=read-write-through " +
    "c_bridge_used=false c_baseline_device=same-nvme c_baseline_scope=in-guest c_baseline_cache=direct " +
    "common_logic_shared=true allocation_per_io=false " +
    "simple_read_iops=120000 simple_write_iops=90000 " +
    "simple_read_p99_us=800 simple_write_p99_us=1000 c_read_iops=100000 " +
    "c_write_iops=80000 c_read_p99_us=900 c_write_p99_us=1100 " +
    "queue_depth=64 warm_runs=5 max_rss_kib=32768\n"
val pure_markers = real_device_q35_pure_simple_boot_markers()
expect(pure_markers).to_contain("storage_provider=simple-driver")
expect(pure_markers).to_contain("network_provider=simple-driver")
expect(pure_markers).to_contain("system_storage_placement=system-driver")
expect(pure_markers).to_contain("storage_grant=resource-grant-set:tok=")
expect(pure_markers).to_contain("network_grant=resource-grant-set:tok=")
expect(pure_markers).to_contain("nvme_perf reason=ready")
expect(pure_markers).to_contain("fat32_direct_io=read-write-through")
expect(pure_markers).to_contain("nvfs_direct_io=read-write-through")
expect(pure_markers).to_contain("dbfs_direct_io=read-write-through")
expect(real_device_q35_pure_simple_serial_accepts_completion(missing_perf)).to_equal(false)
expect(real_device_q35_pure_simple_serial_acceptance_reason(missing_perf)).to_equal("missing-pure-simple-marker:nvme_perf reason=ready")
expect(real_device_q35_pure_simple_serial_accepts_completion(ready_serial)).to_equal(true)
expect(real_device_q35_pure_simple_serial_acceptance_reason(ready_serial)).to_equal("ready")
val spoofed_placement = ready_serial.replace("storage_placement=user-space-driver", "storage_placement=user-space-driver-spoof")
val spoofed_grant = ready_serial.replace("storage_grant=resource-grant-set:tok=101", "storage_grant=resource-grant-set:tokless=101")
expect(real_device_q35_pure_simple_serial_acceptance_reason(spoofed_placement)).to_equal("missing-pure-simple-marker:storage_placement=user-space-driver")
expect(real_device_q35_pure_simple_serial_acceptance_reason(spoofed_grant)).to_equal("missing-pure-simple-marker:storage_grant=resource-grant-set:tok=")
```

</details>

#### builds guest-side pure Simple q35 access and perf markers from measured evidence

- builds guest-side pure Simple q35 access and perf markers from measured evidence
   - Expected: real_device_q35_pure_simple_serial_acceptance_reason(serial) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds guest-side pure Simple q35 access and perf markers from measured evidence")
val access = real_device_q35_pure_simple_access_marker(
    "resource-grant-set:tok=101",
    "resource-grant-set:tok=202"
)
val perf = real_device_q35_pure_simple_perf_marker_from_measurements(
    120000u64,
    90000u64,
    800u64,
    1000u64,
    100000u64,
    80000u64,
    900u64,
    1100u64,
    64u16,
    5u32,
    32768u64,
    false
)
val serial =
    "[stage1] pci_count=7\n" +
    "[stage1] nvme_pci=present\n" +
    "[stage1] nvme_identify_read=pass\n" +
    "[stage1] nvme_rw_restore=pass\n" +
    "[stage1] net_pci=present\n" +
    "[stage1] virtio_net_tx_rx=pass\n" +
    access + "\n" +
    perf + "\n" +
    "TEST PASSED\n"

expect(access).to_contain("storage_provider=simple-driver")
expect(access).to_contain("storage_grant=resource-grant-set:tok=101")
expect(access).to_contain("network_grant=resource-grant-set:tok=202")
expect(perf).to_contain("direct_io_path=nvme-lease-shared-dma-4k")
expect(perf).to_contain("fs_consumers=fat32,nvfs,dbfs")
expect(real_device_q35_pure_simple_serial_acceptance_reason(serial)).to_equal("ready")
```

</details>

#### accepts physical NVMe perf only with pure Simple storage access and real-device identity

- accepts physical NVMe perf only with pure Simple storage access and real-device identity
   - Expected: real_device_physical_nvme_serial_acceptance_reason(access + "\n" + perf + "\nTEST PASSED\n") equals `missing-physical-nvme-marker:user_namespace_assignment=hardware-data-queue`
   - Expected: real_device_physical_nvme_serial_acceptance_reason(access + "\n" + "user_namespace_assignment=hardware-data-queue user_namespace_mode=user-assigned user_namespace_active_lease_count=1 user_namespace_direct_io=read-write-through user_namespace_shared_interface=fat32,nvfs,dbfs user_namespace_conflict_policy=active-lease-checked\n" + extent_sources + perf + "\nTEST PASSED\n") equals `missing-physical-nvme-marker:user_namespace_nsid=`
   - Expected: real_device_physical_nvme_serial_acceptance_reason(access + "\n" + user_namespace + perf + "\nTEST PASSED\n") equals `missing-physical-nvme-marker:fat32_extent_source=freestanding-fat32-extents`
   - Expected: real_device_physical_nvme_serial_acceptance_reason(loose_storage) equals `missing-physical-nvme-marker:storage_placement=user-space-driver`
   - Expected: real_device_physical_nvme_serial_acceptance_reason(loose_assignment) equals `missing-physical-nvme-marker:user_namespace_assignment=hardware-data-queue`
   - Expected: real_device_physical_nvme_serial_acceptance_reason(missing_user_nsid) equals `missing-physical-nvme-marker:user_namespace_nsid=`
   - Expected: real_device_physical_nvme_serial_acceptance_reason(system_user_nsid) equals `physical-nvme-user-namespace-conflicts-system`
   - Expected: real_device_physical_nvme_serial_acceptance_reason(invalid_user_nsid) equals `physical-nvme-user-nsid-invalid`
   - Expected: real_device_physical_nvme_serial_acceptance_reason(system_queue) equals `physical-nvme-user-queue-not-data`
   - Expected: real_device_physical_nvme_serial_acceptance_reason(invalid_queue) equals `physical-nvme-user-queue-invalid`
   - Expected: real_device_physical_nvme_serial_acceptance_reason(missing_active_lease_count) equals `missing-physical-nvme-marker:user_namespace_active_lease_count=`
   - Expected: real_device_physical_nvme_serial_acceptance_reason(missing_shared_interface) equals `missing-physical-nvme-marker:user_namespace_shared_interface=fat32,nvfs,dbfs`
   - Expected: real_device_physical_nvme_serial_acceptance_reason(missing_baseline_device) equals `missing-physical-nvme-marker:c_baseline_device=same-nvme`
   - Expected: real_device_physical_nvme_serial_acceptance_reason(missing_baseline_scope) equals `missing-physical-nvme-marker:c_baseline_scope=in-guest`
   - Expected: real_device_physical_nvme_serial_acceptance_reason(missing_baseline_cache) equals `missing-physical-nvme-marker:c_baseline_cache=direct`
   - Expected: real_device_physical_nvme_serial_acceptance_reason(zero_active_lease_count) equals `physical-nvme-active-lease-check-empty`
   - Expected: real_device_physical_nvme_serial_acceptance_reason(invalid_active_lease_count) equals `physical-nvme-active-lease-count-invalid`
   - Expected: real_device_physical_nvme_serial_acceptance_reason(q35_serial) equals `missing-physical-nvme-marker:hardware_target=real-nvme`
   - Expected: real_device_physical_nvme_serial_acceptance_reason(bridge_serial) equals `storage-not-pure-simple:c-boot-bridge`
   - Expected: real_device_physical_nvme_serial_accepts_completion(serial) is true
   - Expected: real_device_physical_nvme_serial_acceptance_reason(serial) equals `ready`
   - Expected: real_device_physical_nvme_serial_check_command("build/serial/physical-nvme.log") equals `[`
   - Expected: real_device_physical_nvme_validation_script() equals `scripts/run_simpleos_physical_nvme_perf.shs`
   - Expected: real_device_physical_nvme_validation_command("build/serial/physical-nvme.log") equals `[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 156 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts physical NVMe perf only with pure Simple storage access and real-device identity")
val access = real_device_q35_pure_simple_access_marker(
    "resource-grant-set:tok=501",
    "resource-grant-set:tok=none"
)
val user_namespace =
    "user_namespace_assignment=hardware-data-queue user_namespace_mode=user-assigned " +
    "user_namespace_nsid=2 user_namespace_queue_id=2 user_namespace_active_lease_count=1 user_namespace_direct_io=read-write-through user_namespace_shared_interface=fat32,nvfs,dbfs user_namespace_conflict_policy=active-lease-checked\n"
val extent_sources =
    "fat32_extent_source=freestanding-fat32-extents " +
    "nvfs_extent_source=freestanding-dbfs-arena " +
    "dbfs_extent_source=freestanding-dbfs-arena\n"
val perf = real_device_physical_nvme_perf_marker_from_measurements(
    120000u64,
    90000u64,
    800u64,
    1000u64,
    100000u64,
    80000u64,
    900u64,
    1100u64,
    64u16,
    5u32,
    32768u64,
    false,
    "Samsung PM9A3",
    "SN123456",
    1u32
)
val serial = access + "\n" + user_namespace + extent_sources + perf + "\nTEST PASSED\n"
val q35_perf = real_device_q35_pure_simple_perf_marker_from_measurements(
    120000u64,
    90000u64,
    800u64,
    1000u64,
    100000u64,
    80000u64,
    900u64,
    1100u64,
    64u16,
    5u32,
    32768u64,
    false
)
val q35_serial = access + "\n" + user_namespace + extent_sources + q35_perf + "\nTEST PASSED\n"
val bridge_serial = serial.replace("storage_provider=simple-driver", "storage_provider=c-boot-bridge")
val loose_storage = serial.replace("storage_placement=user-space-driver", "storage_placement=user-space-driver-spoof")
val loose_assignment = serial.replace("user_namespace_assignment=hardware-data-queue", "user_namespace_assignment=hardware-data-queue-spoof")
val missing_user_nsid = serial.replace("user_namespace_nsid=2 ", "")
val system_user_nsid = serial.replace("user_namespace_nsid=2", "user_namespace_nsid=1")
val invalid_user_nsid = serial.replace("user_namespace_nsid=2", "user_namespace_nsid=user")
val system_queue = serial.replace("user_namespace_queue_id=2", "user_namespace_queue_id=1")
val invalid_queue = serial.replace("user_namespace_queue_id=2", "user_namespace_queue_id=admin")
val missing_active_lease_count = serial.replace("user_namespace_active_lease_count=1 ", "")
val missing_shared_interface = serial.replace("user_namespace_shared_interface=fat32,nvfs,dbfs ", "")
val missing_baseline_device = serial.replace("c_baseline_device=same-nvme ", "")
val missing_baseline_scope = serial.replace("c_baseline_scope=in-guest ", "")
val missing_baseline_cache = serial.replace("c_baseline_cache=direct ", "")
val zero_active_lease_count = serial.replace("user_namespace_active_lease_count=1", "user_namespace_active_lease_count=0")
val invalid_active_lease_count = serial.replace("user_namespace_active_lease_count=1", "user_namespace_active_lease_count=many")

expect(real_device_physical_nvme_boot_markers()).to_contain("hardware_target=real-nvme")
expect(real_device_physical_nvme_boot_markers()).to_contain("user_namespace_assignment=hardware-data-queue")
expect(real_device_physical_nvme_boot_markers()).to_contain("user_namespace_nsid=")
expect(real_device_physical_nvme_boot_markers()).to_contain("user_namespace_queue_id=")
expect(real_device_physical_nvme_boot_markers()).to_contain("user_namespace_active_lease_count=")
expect(real_device_physical_nvme_boot_markers()).to_contain("user_namespace_shared_interface=fat32,nvfs,dbfs")
expect(real_device_physical_nvme_boot_markers()).to_contain("fat32_direct_io=read-write-through")
expect(real_device_physical_nvme_boot_markers()).to_contain("nvfs_direct_io=read-write-through")
expect(real_device_physical_nvme_boot_markers()).to_contain("dbfs_direct_io=read-write-through")
expect(real_device_physical_nvme_boot_markers()).to_contain("fat32_extent_source=freestanding-fat32-extents")
expect(real_device_physical_nvme_boot_markers()).to_contain("c_baseline_device=same-nvme")
expect(real_device_physical_nvme_boot_markers()).to_contain("c_baseline_scope=in-guest")
expect(real_device_physical_nvme_boot_markers()).to_contain("c_baseline_cache=direct")
expect(real_device_physical_nvme_serial_acceptance_reason(access + "\n" + perf + "\nTEST PASSED\n")).to_equal("missing-physical-nvme-marker:user_namespace_assignment=hardware-data-queue")
expect(real_device_physical_nvme_serial_acceptance_reason(access + "\n" + "user_namespace_assignment=hardware-data-queue user_namespace_mode=user-assigned user_namespace_active_lease_count=1 user_namespace_direct_io=read-write-through user_namespace_shared_interface=fat32,nvfs,dbfs user_namespace_conflict_policy=active-lease-checked\n" + extent_sources + perf + "\nTEST PASSED\n")).to_equal("missing-physical-nvme-marker:user_namespace_nsid=")
expect(real_device_physical_nvme_serial_acceptance_reason(access + "\n" + user_namespace + perf + "\nTEST PASSED\n")).to_equal("missing-physical-nvme-marker:fat32_extent_source=freestanding-fat32-extents")
expect(real_device_physical_nvme_serial_acceptance_reason(loose_storage)).to_equal("missing-physical-nvme-marker:storage_placement=user-space-driver")
expect(real_device_physical_nvme_serial_acceptance_reason(loose_assignment)).to_equal("missing-physical-nvme-marker:user_namespace_assignment=hardware-data-queue")
expect(real_device_physical_nvme_serial_acceptance_reason(missing_user_nsid)).to_equal("missing-physical-nvme-marker:user_namespace_nsid=")
expect(real_device_physical_nvme_serial_acceptance_reason(system_user_nsid)).to_equal("physical-nvme-user-namespace-conflicts-system")
expect(real_device_physical_nvme_serial_acceptance_reason(invalid_user_nsid)).to_equal("physical-nvme-user-nsid-invalid")
expect(real_device_physical_nvme_serial_acceptance_reason(system_queue)).to_equal("physical-nvme-user-queue-not-data")
expect(real_device_physical_nvme_serial_acceptance_reason(invalid_queue)).to_equal("physical-nvme-user-queue-invalid")
expect(real_device_physical_nvme_serial_acceptance_reason(missing_active_lease_count)).to_equal("missing-physical-nvme-marker:user_namespace_active_lease_count=")
expect(real_device_physical_nvme_serial_acceptance_reason(missing_shared_interface)).to_equal("missing-physical-nvme-marker:user_namespace_shared_interface=fat32,nvfs,dbfs")
expect(real_device_physical_nvme_serial_acceptance_reason(missing_baseline_device)).to_equal("missing-physical-nvme-marker:c_baseline_device=same-nvme")
expect(real_device_physical_nvme_serial_acceptance_reason(missing_baseline_scope)).to_equal("missing-physical-nvme-marker:c_baseline_scope=in-guest")
expect(real_device_physical_nvme_serial_acceptance_reason(missing_baseline_cache)).to_equal("missing-physical-nvme-marker:c_baseline_cache=direct")
expect(real_device_physical_nvme_serial_acceptance_reason(zero_active_lease_count)).to_equal("physical-nvme-active-lease-check-empty")
expect(real_device_physical_nvme_serial_acceptance_reason(invalid_active_lease_count)).to_equal("physical-nvme-active-lease-count-invalid")
expect(perf).to_contain("hardware_target=real-nvme")
expect(perf).to_contain("qemu=false")
expect(perf).to_contain("device_model=Samsung_PM9A3")
expect(perf).to_contain("namespace_nsid=1")
expect(real_device_physical_nvme_serial_acceptance_reason(q35_serial)).to_equal("missing-physical-nvme-marker:hardware_target=real-nvme")
expect(real_device_physical_nvme_serial_acceptance_reason(bridge_serial)).to_equal("storage-not-pure-simple:c-boot-bridge")
expect(real_device_physical_nvme_serial_accepts_completion(serial)).to_equal(true)
expect(real_device_physical_nvme_serial_acceptance_reason(serial)).to_equal("ready")

expect(real_device_physical_nvme_serial_check_command("build/serial/physical-nvme.log")).to_equal([
    "bin/release/x86_64-unknown-linux-gnu/simple",
    "run",
    "src/app/simpleos_nvme_serial_check/main.spl",
    "--serial-log", "build/serial/physical-nvme.log"
])
expect(real_device_physical_nvme_validation_script()).to_equal("scripts/run_simpleos_physical_nvme_perf.shs")
expect(real_device_physical_nvme_validation_command("build/serial/physical-nvme.log")).to_equal([
    "sh",
    "scripts/run_simpleos_physical_nvme_perf.shs",
    "--serial-log", "build/serial/physical-nvme.log",
    "--validate-log-only"
])
expect(real_device_physical_nvme_production_validation_command(
    "build/serial/physical-nvme.log",
    "build/serial/physical-nvme-preflight.sdn",
    "build/serial/physical-nvme-validation.sdn"
)).to_equal([
    "sh",
    "scripts/run_simpleos_physical_nvme_perf.shs",
    "--production",
    "--serial-log", "build/serial/physical-nvme.log",
    "--preflight-report", "build/serial/physical-nvme-preflight.sdn",
    "--report-out", "build/serial/physical-nvme-validation.sdn",
    "--validate-log-only"
])
expect(real_device_physical_nvme_live_production_validation_command(
    "/dev/ttyUSB0",
    "115200",
    "30",
    "build/serial/physical-nvme.log",
    "build/serial/physical-nvme-preflight.sdn",
    "build/serial/physical-nvme-validation.sdn"
)).to_equal([
    "env",
    "SERIAL_PORT=/dev/ttyUSB0",
    "SERIAL_BAUD=115200",
    "SIMPLEOS_NVME_DEVICE_GLOB=/dev/nvme*n1",
    "sh",
    "scripts/run_simpleos_physical_nvme_perf.shs",
    "--production",
    "--serial-log", "build/serial/physical-nvme.log",
    "--serial-seconds=30",
    "--preflight-out", "build/serial/physical-nvme-preflight.sdn",
    "--report-out", "build/serial/physical-nvme-validation.sdn"
])
expect(real_device_physical_nvme_live_production_validation_command_for_device_glob(
    "/dev/ttyUSB0",
    "115200",
    "30",
    "/dev/nvme3n1",
    "build/serial/physical-nvme.log",
    "build/serial/physical-nvme-preflight.sdn",
    "build/serial/physical-nvme-validation.sdn"
)).to_contain("SIMPLEOS_NVME_DEVICE_GLOB=/dev/nvme3n1")
```

</details>

#### does not report model or SFFI RDMA as hardware RDMA

- does not report model or SFFI RDMA as hardware RDMA
   - Expected: real_device_readiness_ready(model) is false
   - Expected: real_device_readiness_reason(model) equals `rdma-not-hardware:model`
   - Expected: real_device_readiness_reason(host) equals `rdma-not-hardware:sffi-host`
   - Expected: real_device_readiness_ready(device) is true
   - Expected: real_device_readiness_reason(unsafe) equals `missing-rdma-iommu-or-broker`


<details>
<summary>Executable SSpec</summary>

Runnable source: 74 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not report model or SFFI RDMA as hardware RDMA")
val model = real_device_readiness(
    "x86_64-q35",
    "q35-config-io",
    true,
    "off",
    false,
    false,
    "off",
    false,
    false,
    "model",
    true,
    true,
    true
)
val host = real_device_readiness(
    "x86_64-q35",
    "q35-config-io",
    true,
    "off",
    false,
    false,
    "off",
    false,
    false,
    "sffi-host",
    true,
    true,
    true
)
val device = real_device_readiness_with_providers(
    "x86_64-q35",
    "q35-config-io",
    true,
    "off",
    false,
    false,
    "rdma",
    true,
    true,
    "device",
    true,
    true,
    true,
    "none",
    "none",
    "simple-driver"
)
val unsafe = real_device_readiness_with_providers(
    "x86_64-q35",
    "q35-config-io",
    true,
    "off",
    false,
    false,
    "rdma",
    true,
    true,
    "device",
    true,
    true,
    false,
    "none",
    "none",
    "simple-driver"
)

expect(real_device_readiness_ready(model)).to_equal(false)
expect(real_device_readiness_reason(model)).to_equal("rdma-not-hardware:model")
expect(real_device_readiness_reason(host)).to_equal("rdma-not-hardware:sffi-host")
expect(real_device_readiness_ready(device)).to_equal(true)
expect(real_device_readiness_reason(unsafe)).to_equal("missing-rdma-iommu-or-broker")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/drivers/real_device_readiness_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS real-device readiness.
- SimpleOS real-device readiness

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `bc09ea200ce6f928376b402ba0a1f78c87537601988ce00beaa1b9d863f49a00`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bc09ea200ce6f928376b402ba0a1f78c87537601988ce00beaa1b9d863f49a00`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bc09ea200ce6f928376b402ba0a1f78c87537601988ce00beaa1b9d863f49a00`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/os/drivers/real_device_readiness_spec.spl
mirror: doc/06_spec/unit/os/drivers/real_device_readiness_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/drivers/real_device_readiness_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/drivers/real_device_readiness_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/drivers/real_device_readiness_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/drivers/real_device_readiness_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts q35 NVMe and virtio-net only with hardware evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/drivers/real_device_readiness_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects fallback or incomplete storage and network claims' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/drivers/real_device_readiness_spec.spl:162:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'distinguishes current C bridge evidence from pure Simple driver completion' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
