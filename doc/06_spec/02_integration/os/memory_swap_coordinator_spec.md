# Memory Swap Coordinator Specification

> Tests covering SimpleOS transactional swap coordinator.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Memory Swap Coordinator Specification

## Scenarios

### SimpleOS transactional swap coordinator

#### moves bytes from a mapped frame to block storage and restores them

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- moves bytes from a mapped frame to block storage and restores them
   - Expected: if pmm_init_identity_range(64 * 1024 * 1024, 1024 * 1024, 2 * 1024 * 1024): 1 else: 0 equals `1`
   - Expected: if vmm_init_sparse_for_test(pmm_get_manager(), 0): 1 else: 0 equals `1`
   - Expected: if vmm_map_page(virt, PhysAddr(addr: source), flags): 1 else: 0 equals `1`
   - Expected: coordinator.swap_out_page(allocation.allocation_id, 77, virt.addr, 0, expected.len() as u64).state equals `swapped`
   - Expected: if coordinator.has_swapped_mapping(allocation.allocation_id): 1 else: 0 equals `1`
   - Expected: vmm_read_pte(virt) equals `0`
   - Expected: coordinator.swap_in_page(allocation.allocation_id, 77).state equals `cpu_owned`
   - Expected: memory_vmm_read_physical(restored_phys, expected.len() as u64) equals `expected`
   - Expected: if coordinator.has_swapped_mapping(allocation.allocation_id): 1 else: 0 equals `0`
   - Expected: coordinator.store.snapshot().occupied_slots equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("moves bytes from a mapped frame to block storage and restores them")
mmio_reset_for_test()
expect(if pmm_init_identity_range(64 * 1024 * 1024, 1024 * 1024, 2 * 1024 * 1024): 1 else: 0).to_equal(1)
expect(if vmm_init_sparse_for_test(pmm_get_manager(), 0): 1 else: 0).to_equal(1)
val source = pmm_alloc_page_raw()
val virt = VirtAddr(addr: 0x70000000)
val flags = VmFlags(bits: VM_PRESENT | VM_WRITABLE | VM_USER | VM_NO_EXECUTE)
expect(if vmm_map_page(virt, PhysAddr(addr: source), flags): 1 else: 0).to_equal(1)
val expected: [u8] = [10, 20, 30, 40, 50, 60]
memory_vmm_write_physical(source, expected)

val intent = simple_memory_iso_cpu_cold()
val manager = memory_leveling_manager_new(simpleos_memory_leveling_config_default())
val allocation = manager.request(simple_memory_placement_config_from_intent(intent), memory_leveling_policy_from_intent(intent), expected.len() as u64, 1, 77)
val memory_device = MemBlockDevice.new(32, 512)
val device: BlockDevice = memory_device
val store = memory_swap_block_store_new(true, device, 0, 2, 4096)
val coordinator = memory_swap_coordinator_new(manager, store)

expect(coordinator.swap_out_page(allocation.allocation_id, 77, virt.addr, 0, expected.len() as u64).state).to_equal("swapped")
expect(if coordinator.has_swapped_mapping(allocation.allocation_id): 1 else: 0).to_equal(1)
expect(vmm_read_pte(virt)).to_equal(0)

expect(coordinator.swap_in_page(allocation.allocation_id, 77).state).to_equal("cpu_owned")
val restored_phys = vmm_translate(virt).unwrap().addr
expect(memory_vmm_read_physical(restored_phys, expected.len() as u64)).to_equal(expected)
expect(if coordinator.has_swapped_mapping(allocation.allocation_id): 1 else: 0).to_equal(0)
expect(coordinator.store.snapshot().occupied_slots).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/os/memory_swap_coordinator_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS transactional swap coordinator.
- SimpleOS transactional swap coordinator

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6080baa91ecdc47978502757f707cc38f8caab83f8a7ba992a2889598506e17f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6080baa91ecdc47978502757f707cc38f8caab83f8a7ba992a2889598506e17f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6080baa91ecdc47978502757f707cc38f8caab83f8a7ba992a2889598506e17f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/02_integration/os/memory_swap_coordinator_spec.spl
mirror: doc/06_spec/02_integration/os/memory_swap_coordinator_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/os/memory_swap_coordinator_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/os/memory_swap_coordinator_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/os/memory_swap_coordinator_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/os/memory_swap_coordinator_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'moves bytes from a mapped frame to block storage and restores them' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
