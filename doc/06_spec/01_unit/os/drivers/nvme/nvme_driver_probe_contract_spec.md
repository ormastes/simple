# Nvme Driver Probe Contract Specification

> <details>

<!-- sdn-diagram:id=nvme_driver_probe_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nvme_driver_probe_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nvme_driver_probe_contract_spec -> std
nvme_driver_probe_contract_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nvme_driver_probe_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvme Driver Probe Contract Specification

## Scenarios

### NVMe driver reversible sector probe contract

#### executes the probe through shared transfer commands and structured evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/os/drivers/nvme/nvme_driver_part2.spl")

expect(source.contains("run_reversible_sector_probe")).to_equal(true)
expect(source.contains("self.read_sectors(lba, 1u32, original.phys)")).to_equal(true)
expect(source.contains("self.write_sectors(lba, 1u32, pattern.phys)")).to_equal(true)
expect(source.contains("self.write_sectors(lba, 1u32, original.phys)")).to_equal(true)
expect(source.contains("nvme_sector_probe_result(lba, bytes")).to_equal(true)
expect(source.contains("nvme_sector_probe_result(lba, bytes, completion_status, read_ok, write_ok, restore_ok, true)")).to_equal(true)
```

</details>

#### converts the hardware probe result into standard transfer evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/os/drivers/nvme/nvme_driver_part2.spl")

expect(source.contains("transfer_evidence_from_reversible_probe")).to_equal(true)
expect(source.contains("val probe_result = self.run_reversible_sector_probe(lba)")).to_equal(true)
expect(source.contains("nvme_transfer_evidence(")).to_equal(true)
expect(source.contains("driver_placement")).to_equal(true)
expect(source.contains("grant_kind")).to_equal(true)
expect(source.contains("namespace_mode")).to_equal(true)
```

</details>

#### exposes namespace-aware sector methods before multi-namespace hardware submission

<details>
<summary>Executable SSpec</summary>

Runnable source: 47 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/os/drivers/nvme/nvme_driver_part2.spl")

expect(source.contains("me read_sectors_in_namespace(nsid: u32")).to_equal(true)
expect(source.contains("me write_sectors_in_namespace(nsid: u32")).to_equal(true)
expect(source.contains("me flush_in_namespace(nsid: u32")).to_equal(true)
expect(source.contains("me read_sectors_notify_in_namespace(nsid: u32")).to_equal(true)
expect(source.contains("me write_sectors_notify_in_namespace(nsid: u32")).to_equal(true)
expect(source.contains("me flush_notify_in_namespace(nsid: u32")).to_equal(true)
expect(source.contains("user_io_queues: [NvmeQueuePair]")).to_equal(true)
expect(source.contains("NVME_DRIVER_MAX_DATA_QUEUE_ID: u16 = 3")).to_equal(true)
expect(source.contains("self.set_num_queues(NVME_DRIVER_MAX_DATA_QUEUE_ID, NVME_DRIVER_MAX_DATA_QUEUE_ID)")).to_equal(true)
expect(source.contains("me ensure_user_data_queue(queue_id: u16")).to_equal(true)
expect(source.contains("if queue_id < SIMPLEOS_NVME_FIRST_DATA_QUEUE_ID or queue_id > NVME_DRIVER_MAX_DATA_QUEUE_ID")).to_equal(true)
expect(source.contains("self.user_io_queues.push(queue_result.unwrap())")).to_equal(true)
expect(source.contains("me create_io_queue_pair(qid: u16")).to_equal(true)
expect(source.contains("me read_sectors_in_namespace_on_queue(nsid: u32, queue_id: u16")).to_equal(true)
expect(source.contains("me write_sectors_in_namespace_on_queue(nsid: u32, queue_id: u16")).to_equal(true)
expect(source.contains("me flush_in_namespace_on_queue(nsid: u32, queue_id: u16")).to_equal(true)
expect(source.contains("me read_shared_dma_in_namespace_on_queue(nsid: u32, queue_id: u16")).to_equal(true)
expect(source.contains("me write_shared_dma_in_namespace_on_queue(nsid: u32, queue_id: u16")).to_equal(true)
expect(source.contains("self.read_sectors_in_namespace_on_queue(nsid, queue_id, lba, count, buf.device_addr)")).to_equal(true)
expect(source.contains("self.write_sectors_in_namespace_on_queue(nsid, queue_id, lba, count, buf.device_addr)")).to_equal(true)
expect(source.contains("nvme_flush_io_command_for_namespace(nsid)")).to_equal(true)
expect(source.contains("var g_nvme_user_queue_ids: [u16] = []")).to_equal(true)
expect(source.contains("var g_nvme_user_queue_nsids: [u32] = []")).to_equal(true)
expect(source.contains("var g_nvme_system_queue_nsids: [u32] = []")).to_equal(true)
expect(source.contains("me raw_namespace_queue_access_reason(nsid: u32, queue_id: u16) -> text:")).to_equal(true)
expect(source.contains("if nvme_queue_is_system_reserved(queue_id):")).to_equal(true)
expect(source.contains("self.remember_system_namespace_raw_access(nsid)")).to_equal(true)
expect(source.contains("me ensure_user_data_queue_for_assignment(queue_id: u16, depth: u16, controller_id: u32, nsid: u32, owner_task: u64)")).to_equal(true)
expect(source.contains("val owner_reason = self.user_data_queue_owner_reason(queue_id, depth, controller_id, nsid, owner_task)")).to_equal(true)
expect(source.contains("identified_nsid: 1u32")).to_equal(true)
expect(source.contains("identified_namespaces: [NvmeNamespaceFacts]")).to_equal(true)
expect(source.contains("controller_namespace_count: u32")).to_equal(true)
expect(source.contains("val IDENTITY_CONTROLLER_NN_OFFSET: u64 = 516")).to_equal(true)
expect(source.contains("self.controller_namespace_count = namespace_count")).to_equal(true)
expect(source.contains("me identify_namespace_id(nsid: u32)")).to_equal(true)
expect(source.contains("self.identified_nsid = facts.nsid")).to_equal(true)
expect(source.contains("self.remember_namespace_facts(facts)")).to_equal(true)
expect(source.contains("me identify_first_assignable_user_namespace(excluded_nsid: u32) -> Result<NvmeNamespaceFacts, text>:")).to_equal(true)
expect(source.contains("val fallback_nsid = if excluded_nsid == 2u32: 1u32 else: 2u32")).to_equal(true)
expect(source.contains("val fallback_identify = self.identify_namespace_id(fallback_nsid)")).to_equal(true)
expect(source.contains("if nsid != excluded_nsid:")).to_equal(true)
expect(source.contains("fn namespace_sector_count(nsid: u32)")).to_equal(true)
expect(source.contains("return Result.Err(\"NVMe: namespace not identified\")")).to_equal(true)
expect(source.contains("nvme_read_io_command_for_namespace(nsid")).to_equal(true)
expect(source.contains("nvme_write_io_command_for_namespace(nsid")).to_equal(true)
```

</details>

#### uses one NVMe command per 4K shared-DMA slot instead of one command per 512-byte sector

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/os/drivers/nvme/nvme_driver_part2.spl")

expect(source.contains("\"\"\"Read one 4KiB operation as one multi-sector NVMe command.\"\"\"")).to_equal(true)
expect(source.contains("\"\"\"Write one 4KiB operation as one multi-sector NVMe command.\"\"\"")).to_equal(true)
expect(source.contains("val cmd_result = nvme_read_io_command_for_namespace(nsid, lba, sectors_per_4k, buf.device_addr")).to_equal(true)
expect(source.contains("val cmd_result = nvme_write_io_command_for_namespace(nsid, lba, sectors_per_4k, buf.device_addr")).to_equal(true)
expect(source.contains("val total_commands = lbas.len() as u32")).to_equal(true)
expect(source.contains("val cmd_result = nvme_read_io_command_for_namespace(nsid, base_lba, sectors_per_4k, buf.device_addr + slot_offset")).to_equal(true)
expect(source.contains("val cmd_result = nvme_write_io_command_for_namespace(nsid, base_lba, sectors_per_4k, buf.device_addr + slot_offset")).to_equal(true)
```

</details>

#### routes 4K shared-DMA direct IO through user data queues when assigned

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/os/drivers/nvme/nvme_driver_part2.spl")

expect(source.contains("fn data_queue_depth_for_id(queue_id: u16) -> Result<u16, text>:")).to_equal(true)
expect(source.contains("for existing in self.user_io_queues:")).to_equal(true)
expect(source.contains("if existing.qid == queue_id:")).to_equal(true)
expect(source.contains("status = q.wait_completions(1u32, CMD_TIMEOUT)")).to_equal(true)
expect(source.contains("status = q.wait_completions(total_commands, CMD_TIMEOUT)")).to_equal(true)
expect(source.contains("self.user_io_queues = updated_queues")).to_equal(true)
expect(source.contains("if queue_id != self.io_queue.qid:\n            return Result.Err(\"NVMe: burst queue not ready\")")).to_equal(false)
expect(source.contains("if queue_id != self.io_queue.qid:\n            return Result.Err(\"NVMe: batch queue not ready\")")).to_equal(false)
expect(source.contains("if queue_id != self.io_queue.qid:\n            return Result.Err(\"NVMe: flush queue not ready\")")).to_equal(false)
```

</details>

#### tracks user data queue ownership by controller namespace and owner task

1. var driver = NvmeDriver new
   - Expected: driver.user_data_queue_owner_reason(2u16, 64u16, 0u32, 5u32, 42u64) equals `ready`
2. driver remember user data queue owner
   - Expected: driver.user_data_queue_owner_reason(2u16, 64u16, 0u32, 5u32, 42u64) equals `ready`
   - Expected: driver.user_data_queue_owner_reason(2u16, 64u16, 0u32, 6u32, 42u64) equals `NVMe: user data queue namespace conflict`
   - Expected: driver.user_data_queue_owner_reason(2u16, 64u16, 0u32, 5u32, 43u64) equals `NVMe: user data queue owner conflict`
   - Expected: driver.user_data_queue_owner_reason(2u16, 128u16, 0u32, 5u32, 42u64) equals `NVMe: user data queue depth too small`
   - Expected: driver.release_user_data_queue_owner(2u16, 0u32, 5u32, 43u64) is false
   - Expected: driver.user_data_queue_owner_reason(2u16, 64u16, 0u32, 5u32, 43u64) equals `NVMe: user data queue owner conflict`
   - Expected: driver.release_user_data_queue_owner(2u16, 0u32, 5u32, 42u64) is true
   - Expected: driver.user_data_queue_owner_reason(2u16, 64u16, 0u32, 6u32, 43u64) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var driver = NvmeDriver.new()

expect(driver.user_data_queue_owner_reason(2u16, 64u16, 0u32, 5u32, 42u64)).to_equal("ready")
driver.remember_user_data_queue_owner(2u16, 64u16, 0u32, 5u32, 42u64)
expect(driver.user_data_queue_owner_reason(2u16, 64u16, 0u32, 5u32, 42u64)).to_equal("ready")
expect(driver.user_data_queue_owner_reason(2u16, 64u16, 0u32, 6u32, 42u64)).to_equal("NVMe: user data queue namespace conflict")
expect(driver.user_data_queue_owner_reason(2u16, 64u16, 0u32, 5u32, 43u64)).to_equal("NVMe: user data queue owner conflict")
expect(driver.user_data_queue_owner_reason(2u16, 128u16, 0u32, 5u32, 42u64)).to_equal("NVMe: user data queue depth too small")
expect(driver.release_user_data_queue_owner(2u16, 0u32, 5u32, 43u64)).to_equal(false)
expect(driver.user_data_queue_owner_reason(2u16, 64u16, 0u32, 5u32, 43u64)).to_equal("NVMe: user data queue owner conflict")
expect(driver.release_user_data_queue_owner(2u16, 0u32, 5u32, 42u64)).to_equal(true)
expect(driver.user_data_queue_owner_reason(2u16, 64u16, 0u32, 6u32, 43u64)).to_equal("ready")
```

</details>

#### rejects raw system and user queue access to the same namespace at the driver boundary

1. var driver = NvmeDriver new
   - Expected: driver.raw_namespace_queue_access_reason(5u32, 1u16) equals `ready`
2. driver remember system namespace raw access
   - Expected: driver.raw_namespace_queue_access_reason(5u32, 2u16) equals `NVMe: namespace mode conflict system/user`
   - Expected: driver.user_data_queue_owner_reason(2u16, 64u16, 0u32, 5u32, 42u64) equals `NVMe: namespace mode conflict system/user`
3. var user driver = NvmeDriver new
   - Expected: user_driver.user_data_queue_owner_reason(2u16, 64u16, 0u32, 6u32, 42u64) equals `ready`
4. User driver remember user data queue owner
   - Expected: user_driver.raw_namespace_queue_access_reason(6u32, 1u16) equals `NVMe: namespace mode conflict system/user`
   - Expected: user_driver.raw_namespace_queue_access_reason(6u32, 2u16) equals `ready`
   - Expected: user_driver.raw_namespace_queue_access_reason(7u32, 2u16) equals `NVMe: user data queue namespace conflict`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var driver = NvmeDriver.new()

expect(driver.raw_namespace_queue_access_reason(5u32, 1u16)).to_equal("ready")
driver.remember_system_namespace_raw_access(5u32)
expect(driver.raw_namespace_queue_access_reason(5u32, 2u16)).to_equal("NVMe: namespace mode conflict system/user")
expect(driver.user_data_queue_owner_reason(2u16, 64u16, 0u32, 5u32, 42u64)).to_equal("NVMe: namespace mode conflict system/user")

var user_driver = NvmeDriver.new()
expect(user_driver.user_data_queue_owner_reason(2u16, 64u16, 0u32, 6u32, 42u64)).to_equal("ready")
user_driver.remember_user_data_queue_owner(2u16, 64u16, 0u32, 6u32, 42u64)
expect(user_driver.raw_namespace_queue_access_reason(6u32, 1u16)).to_equal("NVMe: namespace mode conflict system/user")
expect(user_driver.raw_namespace_queue_access_reason(6u32, 2u16)).to_equal("ready")
expect(user_driver.raw_namespace_queue_access_reason(7u32, 2u16)).to_equal("NVMe: user data queue namespace conflict")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/drivers/nvme/nvme_driver_probe_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- NVMe driver reversible sector probe contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
