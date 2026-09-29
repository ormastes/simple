# VMM Kernel PML4 Publish/Read Specification

> Regression spec for `doc/08_tracking/bug/simpleos_vmm_kernel_pml4_phys_reads_zero_after_init_2026-08-06.md`: two parallel VMM implementations printed byte-identical serial banners, but only `os.kernel.arch.x86_64.paging.vmm_init` ran on the live boot path and it stored the kernel PML4 root in its OWN `g_vmm.pml4_phys`. `vmm_core`'s `vmm_kernel_pml4_phys()` — the accessor every downstream consumer (`create_user_address_space`, `vmm_clone_kernel_low_private`, `vmm_copy`) reads — stayed 0 forever, because `vmm_core.spl`'s own `vmm_init` / `vmm_init_from_global_pmm` have zero callers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# VMM Kernel PML4 Publish/Read Specification

Regression spec for `doc/08_tracking/bug/simpleos_vmm_kernel_pml4_phys_reads_zero_after_init_2026-08-06.md`: two parallel VMM implementations printed byte-identical serial banners, but only `os.kernel.arch.x86_64.paging.vmm_init` ran on the live boot path and it stored the kernel PML4 root in its OWN `g_vmm.pml4_phys`. `vmm_core`'s `vmm_kernel_pml4_phys()` — the accessor every downstream consumer (`create_user_address_space`, `vmm_clone_kernel_low_private`, `vmm_copy`) reads — stayed 0 forever, because `vmm_core.spl`'s own `vmm_init` / `vmm_init_from_global_pmm` have zero callers.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-010 |
| Category | Runtime |
| Difficulty | 2/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/os/kernel/memory/vmm_publish_kernel_pml4_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
## Operator workflow
## Compatibility and limitations

# VMM Kernel PML4 Publish/Read Specification

**Feature IDs:** #OS-010
**Category:** Runtime
**Difficulty:** 2/5
**Status:** Implemented
**Requirements:** N/A
**Plan:** N/A
**Design:** N/A
**Research:** N/A

## Overview

Regression spec for
`doc/08_tracking/bug/simpleos_vmm_kernel_pml4_phys_reads_zero_after_init_2026-08-06.md`:
two parallel VMM implementations printed byte-identical serial banners, but
only `os.kernel.arch.x86_64.paging.vmm_init` ran on the live boot path and it
stored the kernel PML4 root in its OWN `g_vmm.pml4_phys`. `vmm_core`'s
`vmm_kernel_pml4_phys()` — the accessor every downstream consumer
(`create_user_address_space`, `vmm_clone_kernel_low_private`, `vmm_copy`)
reads — stayed 0 forever, because `vmm_core.spl`'s own `vmm_init` /
`vmm_init_from_global_pmm` have zero callers.

The fix is `vmm_publish_kernel_pml4(pml4_phys, hhdm_offset)`: the arch paging
layer calls it with ITS locally-live values, and it writes the module-level
SCALARS `_vmm_pml4_phys` / `_vmm_hhdm_offset` / `g_vmm_initialized` (never the
struct global `g_vmm`, which has a constructor initializer — the unreliable
category under freestanding codegen).

This spec exercises the store/load pair at interpreter level: publish a known
PML4 root, then confirm `vmm_kernel_pml4_phys()` reads back the exact value —
not zero, not some other previously-published value. Sabotage check: commenting
out the `_vmm_pml4_phys = pml4_phys` assignment in `vmm_publish_kernel_pml4`
must fail this spec.

## Scenarios

### vmm_publish_kernel_pml4 / vmm_kernel_pml4_phys store-load pair

#### reads back the exact PML4 physical address just published

- Verify: reads back the exact PML4 physical address just published
   - Expected: vmm_kernel_pml4_phys() equals `0x402718720`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_PUBLISH_KERNEL_PM-001
step("Verify: reads back the exact PML4 physical address just published")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
vmm_publish_kernel_pml4(0x402718720, 0x0)
expect(vmm_kernel_pml4_phys()).to_equal(0x402718720)
```

</details>

#### reflects a later publish, proving the accessor is live (not cached/stale)

- Verify: reflects a later publish, proving the accessor is live (not cached/stale)
   - Expected: vmm_kernel_pml4_phys() equals `0x1000`
   - Expected: vmm_kernel_pml4_phys() equals `0x2000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_PUBLISH_KERNEL_PM-001
step("Verify: reflects a later publish, proving the accessor is live (not cached/stale)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
vmm_publish_kernel_pml4(0x1000, 0x0)
expect(vmm_kernel_pml4_phys()).to_equal(0x1000)

vmm_publish_kernel_pml4(0x2000, 0x0)
expect(vmm_kernel_pml4_phys()).to_equal(0x2000)
```

</details>

#### never reads back zero after a nonzero publish (the exact regression)

- Verify: never reads back zero after a nonzero publish (the exact regression)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-MEMORY_VMM_PUBLISH_KERNEL_PM-001
step("Verify: never reads back zero after a nonzero publish (the exact regression)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
vmm_publish_kernel_pml4(0x402718720, 0x0)
expect(vmm_kernel_pml4_phys()).to_be_greater_than(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2f88bd52d195c7b0b0f2f405a225405fac402eea9754a6d98a6beacda3c90763`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2f88bd52d195c7b0b0f2f405a225405fac402eea9754a6d98a6beacda3c90763`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2f88bd52d195c7b0b0f2f405a225405fac402eea9754a6d98a6beacda3c90763`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/kernel/memory/vmm_publish_kernel_pml4_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/memory/vmm_publish_kernel_pml4_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/memory/vmm_publish_kernel_pml4_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/kernel/memory/vmm_publish_kernel_pml4_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/memory/vmm_publish_kernel_pml4_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
