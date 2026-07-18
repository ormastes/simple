# Kernel Vm Fault Specification

> <details>

<!-- sdn-diagram:id=kernel_vm_fault_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=kernel_vm_fault_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

kernel_vm_fault_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=kernel_vm_fault_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Kernel Vm Fault Specification

## Scenarios

### kernel_vm_fault — demand-paging handler

### AC-4: VmaKind constants

#### AC-4: anonymous VMA kind value is defined

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = VmaKind.anonymous
expect(k).to_equal(0)
```

</details>

#### AC-4: guard VMA kind value is defined

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = VmaKind.guard
expect(k).to_equal(1)
```

</details>

#### AC-4: copy-on-write VMA kind value is defined

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = VmaKind.copy_on_write
expect(k).to_equal(2)
```

</details>

#### AC-4: file-backed VMA kind value is defined

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = VmaKind.file_backed
expect(k).to_equal(3)
```

</details>

### AC-4: vm_fault_register_vma — VMA region registration

#### AC-4: register_vma accepts base, size, and kind without error

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# base=0x10000, size=4096 (one page), kind=anonymous
val ok = vm_fault_register_vma(0x10000, 4096, VmaKind.anonymous)
expect(ok).to_equal(true)
```

</details>

#### AC-4: register_vma with guard kind marks the region as guard

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = vm_fault_register_vma(0x20000, 4096, VmaKind.guard)
expect(ok).to_equal(true)
```

</details>

#### AC-4: register_vma with copy-on-write kind succeeds

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = vm_fault_register_vma(0x30000, 4096, VmaKind.copy_on_write)
expect(ok).to_equal(true)
```

</details>

#### AC-4: register_vma rejects zero-size region

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = vm_fault_register_vma(0x40000, 0, VmaKind.anonymous)
expect(ok).to_equal(false)
```

</details>

### AC-4: vm_fault_map_anonymous — page allocation

#### AC-4: map_anonymous returns a non-zero physical frame address

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame_pa = vm_fault_map_anonymous(0x10000)
expect(frame_pa).to_be_greater_than(0)
```

</details>

#### AC-4: map_anonymous for same vaddr in guard region returns zero (fault)

1. vm fault register vma
   - Expected: result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Guard region: expected to return 0 (access fault / kill signal)
vm_fault_register_vma(0x50000, 4096, VmaKind.guard)
val result = vm_fault_map_anonymous(0x50000)
expect(result).to_equal(0)
```

</details>

### AC-4: vm_fault_handle — fault dispatch

#### AC-4: handle on registered anonymous region succeeds with FaultResult.mapped

1. vm fault register vma
   - Expected: result equals `mapped`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
vm_fault_register_vma(0x60000, 4096, VmaKind.anonymous)
val result = vm_fault_handle(0x60000, false)
expect(result).to_equal("mapped")
```

</details>

#### AC-4: handle on guard region returns FaultResult.kill

1. vm fault register vma
   - Expected: result equals `kill`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
vm_fault_register_vma(0x70000, 4096, VmaKind.guard)
val result = vm_fault_handle(0x70000, false)
expect(result).to_equal("kill")
```

</details>

#### AC-4: handle on unregistered region returns FaultResult.unhandled

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# An address with no VMA registered
val result = vm_fault_handle(0xDEAD0000, false)
expect(result).to_equal("unhandled")
```

</details>

#### AC-4: handle on copy-on-write region with write fault returns FaultResult.mapped

1. vm fault register vma
   - Expected: result equals `mapped`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
vm_fault_register_vma(0x80000, 4096, VmaKind.copy_on_write)
val result = vm_fault_handle(0x80000, true)
expect(result).to_equal("mapped")
```

</details>

### AC-4: vm_fault_unregister_vma — VMA deregistration

#### AC-4: unregister removes the region so faults become unhandled

1. vm fault register vma
   - Expected: before equals `mapped`
2. vm fault unregister vma
   - Expected: after equals `unhandled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
vm_fault_register_vma(0x90000, 4096, VmaKind.anonymous)
val before = vm_fault_handle(0x90000, false)
expect(before).to_equal("mapped")
vm_fault_unregister_vma(0x90000, 4096)
val after = vm_fault_handle(0x90000, false)
expect(after).to_equal("unhandled")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/wine/kernel_vm_fault_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- kernel_vm_fault — demand-paging handler
- AC-4: VmaKind constants
- AC-4: vm_fault_register_vma — VMA region registration
- AC-4: vm_fault_map_anonymous — page allocation
- AC-4: vm_fault_handle — fault dispatch
- AC-4: vm_fault_unregister_vma — VMA deregistration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
