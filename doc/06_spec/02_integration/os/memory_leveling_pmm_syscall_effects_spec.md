# Memory Leveling Pmm Syscall Effects Specification

> Tests covering memory-leveling PMM and syscall ownership effects.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Memory Leveling Pmm Syscall Effects Specification

## Scenarios

### memory-leveling PMM and syscall ownership effects

#### allocates and releases a proven contiguous physical range

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- allocates and releases a proven contiguous physical range
   - Expected: pmm_init_identity_range(64 * 1024 * 1024, 1024 * 1024, 2 * 1024 * 1024) is true
   - Expected: (base.addr % 4096) equals `0`
   - Expected: pmm_free_pages() equals `before - 4`
   - Expected: pmm_free_pages() equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("allocates and releases a proven contiguous physical range")
mmio_reset_for_test()
expect(pmm_init_identity_range(64 * 1024 * 1024, 1024 * 1024, 2 * 1024 * 1024)).to_equal(true)
val before = pmm_free_pages()
val base = pmm_alloc_pages(4).unwrap()
expect((base.addr % 4096)).to_equal(0)
expect(pmm_free_pages()).to_equal(before - 4)
pmm_free_page_range(base, 4)
expect(pmm_free_pages()).to_equal(before)
```

</details>

#### rolls back partial mmap and releases every unmapped frame

- rolls back partial mmap and releases every unmapped frame
   - Expected: pmm_init_identity_range(64 * 1024 * 1024, 1024 * 1024, 2 * 1024 * 1024) is true
   - Expected: vmm_init_sparse_for_test(pmm_get_manager(), 0) is true
   - Expected: vmm_map_page(VirtAddr(addr: base_addr), PhysAddr(addr: warm_phys), flags) is true
   - Expected: vmm_unmap_page(VirtAddr(addr: base_addr)) is true
   - Expected: memory_map_owned_pages(base_addr, 2, flags) is false
   - Expected: pmm_free_pages() equals `before`
   - Expected: memory_map_owned_pages(base_addr, 2, flags) is true
   - Expected: pmm_free_pages() equals `before - 2`
   - Expected: pmm_free_pages() equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rolls back partial mmap and releases every unmapped frame")
mmio_reset_for_test()
expect(pmm_init_identity_range(64 * 1024 * 1024, 1024 * 1024, 2 * 1024 * 1024)).to_equal(true)
expect(vmm_init_sparse_for_test(pmm_get_manager(), 0)).to_equal(true)
val flags = VmFlags(bits: VM_PRESENT | VM_WRITABLE | VM_USER | VM_NO_EXECUTE)
val base_addr: u64 = 0x60000000

# Warm the page-table path so the free-page oracle measures leaf frames.
val warm_phys = pmm_alloc_page_raw()
expect(vmm_map_page(VirtAddr(addr: base_addr), PhysAddr(addr: warm_phys), flags)).to_equal(true)
expect(vmm_unmap_page(VirtAddr(addr: base_addr))).to_equal(true)
pmm_free_page_raw(warm_phys)
val before = pmm_free_pages()

vmm_set_map_failure_after_for_test(1)
expect(memory_map_owned_pages(base_addr, 2, flags)).to_equal(false)
vmm_clear_map_failure_for_test()
expect(pmm_free_pages()).to_equal(before)

expect(memory_map_owned_pages(base_addr, 2, flags)).to_equal(true)
expect(pmm_free_pages()).to_equal(before - 2)
memory_release_owned_pages(base_addr, 2)
expect(pmm_free_pages()).to_equal(before)
```

</details>

#### preserves a colliding mapping while cleaning a partial DMA map

- preserves a colliding mapping while cleaning a partial DMA map
   - Expected: pmm_init_identity_range(64 * 1024 * 1024, 1024 * 1024, 2 * 1024 * 1024) is true
   - Expected: vmm_init_sparse_for_test(pmm_get_manager(), 0) is true
   - Expected: vmm_map_page(VirtAddr(addr: base_addr), dma_pages, flags) is true
   - Expected: vmm_map_page(VirtAddr(addr: base_addr + 4096), PhysAddr(addr: unrelated), flags) is true
   - Expected: vmm_translate(VirtAddr(addr: base_addr + 4096)).unwrap().addr equals `unrelated`
   - Expected: vmm_unmap_page(VirtAddr(addr: base_addr + 4096)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("preserves a colliding mapping while cleaning a partial DMA map")
mmio_reset_for_test()
expect(pmm_init_identity_range(64 * 1024 * 1024, 1024 * 1024, 2 * 1024 * 1024)).to_equal(true)
expect(vmm_init_sparse_for_test(pmm_get_manager(), 0)).to_equal(true)
val flags = VmFlags(bits: VM_PRESENT | VM_WRITABLE | VM_USER | VM_NO_EXECUTE)
val base_addr: u64 = 0x61000000
val dma_pages = pmm_alloc_pages(2).unwrap()
val unrelated = pmm_alloc_page_raw()
expect(vmm_map_page(VirtAddr(addr: base_addr), dma_pages, flags)).to_equal(true)
expect(vmm_map_page(VirtAddr(addr: base_addr + 4096), PhysAddr(addr: unrelated), flags)).to_equal(true)

memory_dma_free_partial_pages(base_addr, dma_pages.addr, 1, 2, 4096)

expect(vmm_translate(VirtAddr(addr: base_addr))).to_be_nil()
expect(vmm_translate(VirtAddr(addr: base_addr + 4096)).unwrap().addr).to_equal(unrelated)
expect(vmm_unmap_page(VirtAddr(addr: base_addr + 4096))).to_equal(true)
pmm_free_page_raw(unrelated)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/os/memory_leveling_pmm_syscall_effects_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering memory-leveling PMM and syscall ownership effects.
- memory-leveling PMM and syscall ownership effects

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `6f84ed90d7a47f7331daf19f991a9eada0f5087cef052587944199500fc0855b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6f84ed90d7a47f7331daf19f991a9eada0f5087cef052587944199500fc0855b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6f84ed90d7a47f7331daf19f991a9eada0f5087cef052587944199500fc0855b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/02_integration/os/memory_leveling_pmm_syscall_effects_spec.spl
mirror: doc/06_spec/02_integration/os/memory_leveling_pmm_syscall_effects_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/os/memory_leveling_pmm_syscall_effects_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/os/memory_leveling_pmm_syscall_effects_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/os/memory_leveling_pmm_syscall_effects_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/os/memory_leveling_pmm_syscall_effects_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allocates and releases a proven contiguous physical range' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/os/memory_leveling_pmm_syscall_effects_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rolls back partial mmap and releases every unmapped frame' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/os/memory_leveling_pmm_syscall_effects_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves a colliding mapping while cleaning a partial DMA map' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
