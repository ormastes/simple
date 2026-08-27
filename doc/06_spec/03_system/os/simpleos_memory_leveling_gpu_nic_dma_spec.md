# Simpleos Memory Leveling Gpu Nic Dma Specification

> Tests covering SimpleOS GPU NIC DMA memory leveling.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Memory Leveling Gpu Nic Dma Specification

## Scenarios

### SimpleOS GPU NIC DMA memory leveling

#### REQ-001 REQ-002 keeps language and kernel configurations separate

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- REQ-001 REQ-002 keeps language and kernel configurations separate
- Create an independently owned language placement configuration
- Create an independently owned SimpleOS capacity configuration
- Verify neither configuration mutation changes the other owner
   - Expected: placement.preferred_tier.name equals `cpu_cold`
   - Expected: placement.movable is false
   - Expected: os_config.pressure_batch_limit equals `5`
   - Expected: os_config.swap_enabled is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-001 REQ-002 keeps language and kernel configurations separate")
step("Create an independently owned language placement configuration")
val intent = simple_memory_iso_cpu_cold()
var placement = simple_memory_placement_config_from_intent(intent)

step("Create an independently owned SimpleOS capacity configuration")
var os_config = simpleos_memory_leveling_config_default()
placement.movable = false
os_config.pressure_batch_limit = 5

step("Verify neither configuration mutation changes the other owner")
expect(placement.preferred_tier.name).to_equal("cpu_cold")
expect(placement.movable).to_equal(false)
expect(os_config.pressure_batch_limit).to_equal(5)
expect(os_config.swap_enabled).to_equal(true)
```

</details>

#### REQ-003 REQ-005 REQ-006 enforces identity ownership pins and DMA order

- REQ-003 REQ-005 REQ-006 enforces identity ownership pins and DMA order
- Allocate a tracked cold CPU buffer with stable identity
   - Expected: allocation.ok is true
- Reject ownership transfer before a device mapping exists
   - Expected: manager.sync_for_device(allocation.allocation_id, 91).reason equals `sync-required`
- Balance nested pins before transferring ownership
   - Expected: manager.pin(allocation.allocation_id, 91).ok is true
   - Expected: manager.pin(allocation.allocation_id, 91).ok is true
   - Expected: manager.unpin(allocation.allocation_id, 91).ok is true
   - Expected: manager.unpin(allocation.allocation_id, 91).ok is true
- Map synchronize submit complete and synchronize back to CPU
   - Expected: manager.map_device(allocation.allocation_id, 91, MEMORY_DMA_DIRECTION_BIDIRECTIONAL, true).state equals `syncing_for_device`
   - Expected: manager.sync_for_device(allocation.allocation_id, 91).state equals `device_owned`
   - Expected: manager.begin_in_flight(allocation.allocation_id, 91).ok is true
   - Expected: manager.release(allocation.allocation_id, 91).reason equals `protected`
   - Expected: manager.complete_in_flight(allocation.allocation_id, 91).ok is true
   - Expected: manager.sync_for_cpu(allocation.allocation_id, 91).state equals `syncing_for_cpu`
   - Expected: manager.unmap_device(allocation.allocation_id, 91).state equals `cpu_owned`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-003 REQ-005 REQ-006 enforces identity ownership pins and DMA order")
step("Allocate a tracked cold CPU buffer with stable identity")
val intent = simple_memory_iso_cpu_cold()
val manager = memory_leveling_manager_new(simpleos_memory_leveling_config_default())
val allocation = manager.request(simple_memory_placement_config_from_intent(intent), memory_leveling_policy_from_intent(intent), 4096, 1, 91)
expect(allocation.ok).to_equal(true)

step("Reject ownership transfer before a device mapping exists")
expect(manager.sync_for_device(allocation.allocation_id, 91).reason).to_equal("sync-required")

step("Balance nested pins before transferring ownership")
expect(manager.pin(allocation.allocation_id, 91).ok).to_equal(true)
expect(manager.pin(allocation.allocation_id, 91).ok).to_equal(true)
expect(manager.unpin(allocation.allocation_id, 91).ok).to_equal(true)
expect(manager.unpin(allocation.allocation_id, 91).ok).to_equal(true)

step("Map synchronize submit complete and synchronize back to CPU")
expect(manager.map_device(allocation.allocation_id, 91, MEMORY_DMA_DIRECTION_BIDIRECTIONAL, true).state).to_equal("syncing_for_device")
expect(manager.sync_for_device(allocation.allocation_id, 91).state).to_equal("device_owned")
expect(manager.begin_in_flight(allocation.allocation_id, 91).ok).to_equal(true)
expect(manager.release(allocation.allocation_id, 91).reason).to_equal("protected")
expect(manager.complete_in_flight(allocation.allocation_id, 91).ok).to_equal(true)
expect(manager.sync_for_cpu(allocation.allocation_id, 91).state).to_equal("syncing_for_cpu")
expect(manager.unmap_device(allocation.allocation_id, 91).state).to_equal("cpu_owned")
```

</details>

#### REQ-008 REQ-014 bounds pressure and reports incremental counters

- REQ-008 REQ-014 bounds pressure and reports incremental counters
- Configure a pressure batch larger than the hard safety bound
- Apply critical pressure without scanning every allocation
   - Expected: report.inspected equals `64`
   - Expected: report.selected equals `64`
- Inspect maintained counters without a registry scan
   - Expected: stats.allocation_count equals `70`
   - Expected: stats.cpu_bytes equals `70 * 4096`
   - Expected: stats.candidate_count equals `70`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-008 REQ-014 bounds pressure and reports incremental counters")
step("Configure a pressure batch larger than the hard safety bound")
var config = simpleos_memory_leveling_config_default()
config.pressure_batch_limit = 1000
val manager = memory_leveling_manager_new(config)
val intent = simple_memory_iso_cpu_cold()
var i: u64 = 0
while i < 70:
    manager.request(simple_memory_placement_config_from_intent(intent), memory_leveling_policy_from_intent(intent), 4096, 1, i + 1)
    i = i + 1

step("Apply critical pressure without scanning every allocation")
val report = manager.apply_pressure("critical")
expect(report.inspected).to_equal(64)
expect(report.selected).to_equal(64)

step("Inspect maintained counters without a registry scan")
val stats = manager.snapshot()
expect(stats.allocation_count).to_equal(70)
expect(stats.cpu_bytes).to_equal(70 * 4096)
expect(stats.candidate_count).to_equal(70)
```

</details>

#### REQ-007 preserves CPU and device reservations

- REQ-007 preserves CPU and device reservations
- Configure CPU GPU NIC and DMA reservations over shared capacity
- Reject CPU allocation that would consume protected device capacity
   - Expected: manager.request(simple_memory_placement_config_from_intent(cpu), memory_leveling_policy_from_intent(cpu), 71, 1, 1).reason equals `reservation-protected`
   - Expected: manager.request(simple_memory_placement_config_from_intent(cpu), memory_leveling_policy_from_intent(cpu), 70, 1, 1).ok is true
- Consume the GPU reservation without starving the CPU reserve
   - Expected: manager.request(simple_memory_placement_config_from_intent(gpu_intent), memory_leveling_policy_from_intent(gpu_intent), 10, 1, 2).ok is true
   - Expected: manager.request(simple_memory_placement_config_from_intent(gpu_intent), memory_leveling_policy_from_intent(gpu_intent), 1, 1, 2).reason equals `reservation-protected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-007 preserves CPU and device reservations")
step("Configure CPU GPU NIC and DMA reservations over shared capacity")
var config = simpleos_memory_leveling_config_default()
config.physical_capacity_bytes = 100
config.cpu_capacity_bytes = 100
config.cpu_reserved_bytes = 20
config.cpu_low_watermark_bytes = 25
config.cpu_high_watermark_bytes = 50
config.gpu_capacity_bytes = 50
config.gpu_reserved_bytes = 10
config.nic_reserved_bytes = 10
config.dma_reserved_bytes = 10
val manager = memory_leveling_manager_new(config)

step("Reject CPU allocation that would consume protected device capacity")
val cpu = simple_memory_iso_cpu_cold()
expect(manager.request(simple_memory_placement_config_from_intent(cpu), memory_leveling_policy_from_intent(cpu), 71, 1, 1).reason).to_equal("reservation-protected")
expect(manager.request(simple_memory_placement_config_from_intent(cpu), memory_leveling_policy_from_intent(cpu), 70, 1, 1).ok).to_equal(true)

step("Consume the GPU reservation without starving the CPU reserve")
val gpu_intent = simple_memory_device_gpu()
expect(manager.request(simple_memory_placement_config_from_intent(gpu_intent), memory_leveling_policy_from_intent(gpu_intent), 10, 1, 2).ok).to_equal(true)
expect(manager.request(simple_memory_placement_config_from_intent(gpu_intent), memory_leveling_policy_from_intent(gpu_intent), 1, 1, 2).reason).to_equal("reservation-protected")
```

</details>

#### REQ-009 preserves bytes across committed swap transitions

- REQ-009 preserves bytes across committed swap transitions
- Prepare a cold allocation for swap
   - Expected: manager.prepare_swap(allocation.allocation_id, 31).state equals `migrating`
- Write deterministic bytes before committing the swapped state
   - Expected: written.ok is true
   - Expected: manager.commit_swap(allocation.allocation_id, 31, written.slot_id).state equals `swapped`
- Validate all bytes before committing restore and releasing the slot
   - Expected: manager.prepare_restore(allocation.allocation_id, 31).state equals `migrating`
   - Expected: restored.bytes equals `expected`
   - Expected: manager.commit_restore(allocation.allocation_id, 31).state equals `cpu_owned`
   - Expected: store.release(written.slot_id, allocation.allocation_id).ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-009 preserves bytes across committed swap transitions")
step("Prepare a cold allocation for swap")
val intent = simple_memory_iso_cpu_cold()
val manager = memory_leveling_manager_new(simpleos_memory_leveling_config_default())
val store = memory_swap_store_new(true, 1)
val allocation = manager.request(simple_memory_placement_config_from_intent(intent), memory_leveling_policy_from_intent(intent), 4, 1, 31)
expect(manager.prepare_swap(allocation.allocation_id, 31).state).to_equal("migrating")

step("Write deterministic bytes before committing the swapped state")
val expected: [u8] = [222, 173, 190, 239]
val written = store.write(allocation.allocation_id, 0, expected)
expect(written.ok).to_equal(true)
expect(manager.commit_swap(allocation.allocation_id, 31, written.slot_id).state).to_equal("swapped")

step("Validate all bytes before committing restore and releasing the slot")
expect(manager.prepare_restore(allocation.allocation_id, 31).state).to_equal("migrating")
val restored = store.read(written.slot_id, allocation.allocation_id, 0)
expect(restored.bytes).to_equal(expected)
expect(manager.commit_restore(allocation.allocation_id, 31).state).to_equal("cpu_owned")
expect(store.release(written.slot_id, allocation.allocation_id).ok).to_equal(true)
```

</details>

#### REQ-011 validates scatter DMA metadata and synchronization

- REQ-011 validates scatter DMA metadata and synchronization
- Create a DMA descriptor with two explicit physical segments
   - Expected: mapping.segment_count() equals `2`
- Transfer ownership in order and reject unmap while device-owned
   - Expected: dma_mapping_unmap(device).is_err() is true
   - Expected: dma_mapping_unmap(returned).is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-011 validates scatter DMA metadata and synchronization")
step("Create a DMA descriptor with two explicit physical segments")
val buffer = SharedDmaBuffer(
    cpu_virt_addr: 0x1000,
    host_phys_addr: 0x8000,
    device_addr: 0xA000,
    byte_len: 4096,
    cache_policy: DmaCachePolicy.Coherent,
    owner: DmaOwner(task_id: 4, bdf_bus: 0, bdf_device: 2, bdf_function: 0),
    allocation_id: 88
)
val layout = dma_scatter_layout([
    dma_segment(0x1000, 0x8000, 0xA000, 2048),
    dma_segment(0x1800, 0xC000, 0xE000, 2048)
])
val mapping = dma_shared_mapping(buffer, DmaDir.Bidirectional, layout, 17).unwrap()
expect(mapping.segment_count()).to_equal(2)

step("Transfer ownership in order and reject unmap while device-owned")
val cpu = dma_mapping_map(mapping).unwrap()
val device = dma_mapping_sync_for_device(cpu).unwrap()
expect(dma_mapping_unmap(device).is_err()).to_equal(true)
val returned = dma_mapping_sync_for_cpu(device).unwrap()
expect(dma_mapping_unmap(returned).is_ok()).to_equal(true)
```

</details>

#### REQ-012 protects GPU queues and NIC buffers through completion

- REQ-012 protects GPU queues and NIC buffers through completion
- Register a permanently pinned GPU command queue
   - Expected: manager.register_gpu_queue(501, 12, 4096, 0x12000).ok is true
- Submit and complete GPU work while release remains protected
   - Expected: manager.device_submit(501, 12).state equals `device_owned`
   - Expected: manager.release(501, 12).reason equals `protected`
   - Expected: manager.device_complete(501, 12).state equals `syncing_for_cpu`
   - Expected: manager.device_unmap(501, 12).state equals `cpu_owned`
   - Expected: manager.release(501, 12).reason equals `protected`
- Release a temporary NIC buffer only after its completion
   - Expected: manager.register_nic_buffer(502, 13, 2048, 0x14000, true).ok is true
   - Expected: manager.device_submit(502, 13).ok is true
   - Expected: manager.release(502, 13).reason equals `protected`
   - Expected: manager.device_complete(502, 13).ok is true
   - Expected: manager.device_unmap(502, 13).ok is true
   - Expected: manager.release(502, 13).ok is true
   - Expected: memory_leveling_device_migration_unavailable(502).reason equals `migration-unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-012 protects GPU queues and NIC buffers through completion")
step("Register a permanently pinned GPU command queue")
var config = simpleos_memory_leveling_config_default()
config.gpu_capacity_bytes = 65536
config.nic_capacity_bytes = 65536
config.nic_reserved_bytes = 0
val manager = memory_leveling_manager_new(config)
expect(manager.register_gpu_queue(501, 12, 4096, 0x12000).ok).to_equal(true)

step("Submit and complete GPU work while release remains protected")
expect(manager.device_submit(501, 12).state).to_equal("device_owned")
expect(manager.release(501, 12).reason).to_equal("protected")
expect(manager.device_complete(501, 12).state).to_equal("syncing_for_cpu")
expect(manager.device_unmap(501, 12).state).to_equal("cpu_owned")
expect(manager.release(501, 12).reason).to_equal("protected")

step("Release a temporary NIC buffer only after its completion")
expect(manager.register_nic_buffer(502, 13, 2048, 0x14000, true).ok).to_equal(true)
expect(manager.device_submit(502, 13).ok).to_equal(true)
expect(manager.release(502, 13).reason).to_equal("protected")
expect(manager.device_complete(502, 13).ok).to_equal(true)
expect(manager.device_unmap(502, 13).ok).to_equal(true)
expect(manager.release(502, 13).ok).to_equal(true)
expect(memory_leveling_device_migration_unavailable(502).reason).to_equal("migration-unavailable")
```

</details>

#### REQ-013 REQ-015 reports QEMU support without hardware overclaim

- REQ-013 REQ-015 reports QEMU support without hardware overclaim
- Inspect the QEMU virtio capability report
   - Expected: capabilities.virtio_gpu_backing is true
   - Expected: capabilities.virtio_nic_buffers is true
   - Expected: capabilities.contiguous_dma is true
- Reject physical GPU NIC GPUDirect RDMA and IOMMU claims
   - Expected: memory_leveling_can_migrate_gpu(capabilities) is false
   - Expected: memory_leveling_can_migrate_nic(capabilities) is false
   - Expected: capabilities.gpudirect is false
   - Expected: capabilities.rdma_paging is false
   - Expected: capabilities.iommu_isolation is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-013 REQ-015 reports QEMU support without hardware overclaim")
step("Inspect the QEMU virtio capability report")
val capabilities = memory_leveling_qemu_capabilities()
expect(capabilities.virtio_gpu_backing).to_equal(true)
expect(capabilities.virtio_nic_buffers).to_equal(true)
expect(capabilities.contiguous_dma).to_equal(true)

step("Reject physical GPU NIC GPUDirect RDMA and IOMMU claims")
expect(memory_leveling_can_migrate_gpu(capabilities)).to_equal(false)
expect(memory_leveling_can_migrate_nic(capabilities)).to_equal(false)
expect(capabilities.gpudirect).to_equal(false)
expect(capabilities.rdma_paging).to_equal(false)
expect(capabilities.iommu_isolation).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/simpleos_memory_leveling_gpu_nic_dma_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS GPU NIC DMA memory leveling.
- SimpleOS GPU NIC DMA memory leveling

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

- `REQ-SSPEC-SYSTEM`
- `REQ-002`
- `REQ-005`
- `REQ-006`
- `REQ-014`
- `REQ-015`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `98ff2046848fa810e7beff27b2bf56cea08eab3fd9fac5c563760f3aca44ba75`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `98ff2046848fa810e7beff27b2bf56cea08eab3fd9fac5c563760f3aca44ba75`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `98ff2046848fa810e7beff27b2bf56cea08eab3fd9fac5c563760f3aca44ba75`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/os/simpleos_memory_leveling_gpu_nic_dma_spec.spl
mirror: doc/06_spec/03_system/os/simpleos_memory_leveling_gpu_nic_dma_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/simpleos_memory_leveling_gpu_nic_dma_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/simpleos_memory_leveling_gpu_nic_dma_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/simpleos_memory_leveling_gpu_nic_dma_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/simpleos_memory_leveling_gpu_nic_dma_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-001 REQ-002 keeps language and kernel configurations separate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos_memory_leveling_gpu_nic_dma_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-003 REQ-005 REQ-006 enforces identity ownership pins and DMA order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos_memory_leveling_gpu_nic_dma_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-008 REQ-014 bounds pressure and reports incremental counters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
