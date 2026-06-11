# Wine Kernel32 Virtual Memory Specification

> 1. wine vm space new

<!-- sdn-diagram:id=wine_kernel32_virtual_memory_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_kernel32_virtual_memory_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_kernel32_virtual_memory_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_kernel32_virtual_memory_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Kernel32 Virtual Memory Specification

## Scenarios

### Wine KERNEL32 virtual memory bridge

#### executes a bounded allocate-protect-free sequence through the VM adapter

1. wine vm space new
   - Expected: result.ok is true
   - Expected: result.base equals `0x700000`
   - Expected: result.size equals `0x2000`
   - Expected: result.old_perms equals `rw`
   - Expected: result.operations equals `VirtualAlloc VirtualProtect VirtualFree`
   - Expected: wine_vm_access_gate(result.space, 0x700000, "read") equals `page-fault-unmapped`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_kernel32_execute_virtual_memory(
    ["VirtualAlloc", "VirtualProtect", "VirtualFree"],
    wine_vm_space_new(),
    0x700000,
    0x2000,
    "rw",
    "rx"
)

expect(result.ok).to_equal(true)
expect(result.base).to_equal(0x700000)
expect(result.size).to_equal(0x2000)
expect(result.old_perms).to_equal("rw")
expect(result.operations).to_equal("VirtualAlloc VirtualProtect VirtualFree")
expect(wine_vm_access_gate(result.space, 0x700000, "read")).to_equal("page-fault-unmapped")
```

</details>

#### keeps virtual memory dispatch ordered and bounded

1. wine vm space new
   - Expected: out_of_order.ok is false
   - Expected: out_of_order.error equals `kernel32-virtual-memory-sequence-expected:VirtualAlloc`
2. wine vm space new
   - Expected: wrong_family.ok is false
   - Expected: wrong_family.error equals `bridge-wrong-category:GetCommandLineW`
3. wine vm space new
   - Expected: invalid.ok is false
   - Expected: invalid.error equals `VirtualAlloc:invalid-size`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out_of_order = wine_kernel32_execute_virtual_memory(
    ["VirtualProtect", "VirtualAlloc", "VirtualFree"],
    wine_vm_space_new(),
    0x710000,
    0x1000,
    "rw",
    "rx"
)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("kernel32-virtual-memory-sequence-expected:VirtualAlloc")

val wrong_family = wine_kernel32_execute_virtual_memory(
    ["VirtualAlloc", "GetCommandLineW", "VirtualFree"],
    wine_vm_space_new(),
    0x720000,
    0x1000,
    "rw",
    "rx"
)
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:GetCommandLineW")

val invalid = wine_kernel32_execute_virtual_memory(
    ["VirtualAlloc", "VirtualProtect", "VirtualFree"],
    wine_vm_space_new(),
    0x730000,
    0,
    "rw",
    "rx"
)
expect(invalid.ok).to_equal(false)
expect(invalid.error).to_equal("VirtualAlloc:invalid-size")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_kernel32_virtual_memory_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine KERNEL32 virtual memory bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
