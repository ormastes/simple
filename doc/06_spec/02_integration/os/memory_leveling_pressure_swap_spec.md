# Memory Leveling Pressure Swap Specification

> Tests covering SimpleOS pressure-driven swap.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Memory Leveling Pressure Swap Specification

## Scenarios

### SimpleOS pressure-driven swap

#### selects a bounded mapped page swaps it and restores on fault

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- selects a bounded mapped page swaps it and restores on fault
   - Expected: if pmm_init_identity_range(64 * 1024 * 1024, 1024 * 1024, 2 * 1024 * 1024): 1 else: 0 equals `1`
   - Expected: if vmm_init_sparse_for_test(pmm_get_manager(), 0): 1 else: 0 equals `1`
   - Expected: if vmm_map_page(virt, PhysAddr(addr: source), flags): 1 else: 0 equals `1`
   - Expected: registered.ok is true
   - Expected: memory_swap_runtime_install_block_device(device, 0, 2) equals `ok`
   - Expected: pressure.report.level equals `critical`
   - Expected: pressure.report.inspected equals `1`
   - Expected: pressure.swapped equals `1`
   - Expected: pressure.failed equals `0`
   - Expected: vmm_read_pte(virt) equals `0`
   - Expected: memory_swap_runtime_last_fault_reason() equals `ok`
   - Expected: fault_result equals `0`
   - Expected: restored_allocation.state.name equals `cpu_owned`
   - Expected: memory_vmm_read_physical(restored, expected.len() as u64) equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("selects a bounded mapped page swaps it and restores on fault")
mmio_reset_for_test()
memory_swap_runtime_clear_for_test()
expect(if pmm_init_identity_range(64 * 1024 * 1024, 1024 * 1024, 2 * 1024 * 1024): 1 else: 0).to_equal(1)
expect(if vmm_init_sparse_for_test(pmm_get_manager(), 0): 1 else: 0).to_equal(1)
var config = simpleos_memory_leveling_config_default()
config.pressure_batch_limit = 4
config.cpu_low_watermark_bytes = 64 * 1024 * 1024
config.cpu_high_watermark_bytes = 64 * 1024 * 1024
memory_leveling_runtime_init(config)

val source = pmm_alloc_page_raw()
val virt = VirtAddr(addr: 0x72000000)
val flags = VmFlags(bits: VM_PRESENT | VM_WRITABLE | VM_USER | VM_NO_EXECUTE)
expect(if vmm_map_page(virt, PhysAddr(addr: source), flags): 1 else: 0).to_equal(1)
val expected: [u8] = [2, 4, 6, 8, 10]
memory_vmm_write_physical(source, expected)
val registered = memory_leveling_runtime_register_cpu_range(virt.addr, expected.len() as u64, 99)
expect(registered.ok).to_equal(true)

val memory_device = MemBlockDevice.new(32, 512)
val device: BlockDevice = memory_device
expect(memory_swap_runtime_install_block_device(device, 0, 2)).to_equal("ok")

val pressure = memory_swap_runtime_poll_pmm_pressure()
expect(pressure.report.level).to_equal("critical")
expect(pressure.report.inspected).to_equal(1)
expect(pressure.swapped).to_equal(1)
expect(pressure.failed).to_equal(0)
expect(vmm_read_pte(virt)).to_equal(0)

val fault_result = memory_swap_runtime_handle_fault(virt.addr)
expect(memory_swap_runtime_last_fault_reason()).to_equal("ok")
expect(fault_result).to_equal(0)
val runtime_manager = memory_leveling_runtime_manager()
val restored_allocation = runtime_manager.get(registered.allocation_ids[0]).unwrap()
expect(restored_allocation.state.name).to_equal("cpu_owned")
val restored = vmm_translate(virt).unwrap().addr
expect(memory_vmm_read_physical(restored, expected.len() as u64)).to_equal(expected)
```

</details>

#### releases a swapped slot on munmap so capacity is reusable

- releases a swapped slot on munmap so capacity is reusable
   - Expected: pmm_init_identity_range(64 * 1024 * 1024, 1024 * 1024, 2 * 1024 * 1024) is true
   - Expected: vmm_init_sparse_for_test(pmm_get_manager(), 0) is true
   - Expected: memory_swap_runtime_install_block_device(device, 0, 1) equals `ok`
   - Expected: vmm_map_page(first_virt, PhysAddr(addr: first_phys), flags) is true
   - Expected: memory_leveling_runtime_register_cpu_range(first_virt.addr, 4096, 77).ok is true
   - Expected: memory_swap_runtime_poll_pmm_pressure().swapped equals `1`
   - Expected: memory_swap_runtime_release_range(first_virt.addr, 4096, 77).ok is true
   - Expected: vmm_map_page(second_virt, PhysAddr(addr: second_phys), flags) is true
   - Expected: memory_leveling_runtime_register_cpu_range(second_virt.addr, 4096, 77).ok is true
   - Expected: memory_swap_runtime_poll_pmm_pressure().swapped equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("releases a swapped slot on munmap so capacity is reusable")
mmio_reset_for_test()
memory_swap_runtime_clear_for_test()
expect(pmm_init_identity_range(64 * 1024 * 1024, 1024 * 1024, 2 * 1024 * 1024)).to_equal(true)
expect(vmm_init_sparse_for_test(pmm_get_manager(), 0)).to_equal(true)
var config = simpleos_memory_leveling_config_default()
config.cpu_low_watermark_bytes = 64 * 1024 * 1024
config.cpu_high_watermark_bytes = 64 * 1024 * 1024
memory_leveling_runtime_init(config)
val memory_device = MemBlockDevice.new(8, 512)
val device: BlockDevice = memory_device
expect(memory_swap_runtime_install_block_device(device, 0, 1)).to_equal("ok")

val first_phys = pmm_alloc_page_raw()
val first_virt = VirtAddr(addr: 0x73000000)
val flags = VmFlags(bits: VM_PRESENT | VM_WRITABLE | VM_USER | VM_NO_EXECUTE)
expect(vmm_map_page(first_virt, PhysAddr(addr: first_phys), flags)).to_equal(true)
expect(memory_leveling_runtime_register_cpu_range(first_virt.addr, 4096, 77).ok).to_equal(true)
expect(memory_swap_runtime_poll_pmm_pressure().swapped).to_equal(1)
expect(memory_swap_runtime_release_range(first_virt.addr, 4096, 77).ok).to_equal(true)

val second_phys = pmm_alloc_page_raw()
val second_virt = VirtAddr(addr: 0x73001000)
expect(vmm_map_page(second_virt, PhysAddr(addr: second_phys), flags)).to_equal(true)
expect(memory_leveling_runtime_register_cpu_range(second_virt.addr, 4096, 77).ok).to_equal(true)
expect(memory_swap_runtime_poll_pmm_pressure().swapped).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/os/memory_leveling_pressure_swap_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS pressure-driven swap.
- SimpleOS pressure-driven swap

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `1ab63d8804a25d38c3b46327eea47f317a56fb8374ad4fa322998ec623736b0b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1ab63d8804a25d38c3b46327eea47f317a56fb8374ad4fa322998ec623736b0b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1ab63d8804a25d38c3b46327eea47f317a56fb8374ad4fa322998ec623736b0b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/02_integration/os/memory_leveling_pressure_swap_spec.spl
mirror: doc/06_spec/02_integration/os/memory_leveling_pressure_swap_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/os/memory_leveling_pressure_swap_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/os/memory_leveling_pressure_swap_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/os/memory_leveling_pressure_swap_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/os/memory_leveling_pressure_swap_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects a bounded mapped page swaps it and restores on fault' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/os/memory_leveling_pressure_swap_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'releases a swapped slot on munmap so capacity is reusable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
