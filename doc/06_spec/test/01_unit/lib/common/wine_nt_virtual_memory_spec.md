# Wine Nt Virtual Memory Specification

> <details>

<!-- sdn-diagram:id=wine_nt_virtual_memory_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_nt_virtual_memory_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_nt_virtual_memory_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_nt_virtual_memory_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Nt Virtual Memory Specification

## Scenarios

### Wine NT virtual memory bridge

#### lists the modeled VirtualAlloc, VirtualProtect, and VirtualFree calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val calls = wine_nt_virtual_memory_required_calls()
expect(calls.len()).to_equal(3)
expect(calls[0]).to_equal("VirtualAlloc")
```

</details>

#### allocates automatic committed memory through the VM adapter

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val allocated = wine_nt_virtual_memory_alloc(wine_vm_space_new(), 0, 0x2000, "rw")
expect(allocated.ok).to_equal(true)
expect(allocated.state).to_equal("allocated")
expect(allocated.base).to_equal(0x10000000)
expect(wine_vm_access_gate(allocated.space, allocated.base, "write")).to_equal("ready")
```

</details>

#### allocates fixed memory and rejects fixed overlap

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first = wine_nt_virtual_memory_alloc(wine_vm_space_new(), 0x400000, 0x2000, "rw")
val second = wine_nt_virtual_memory_alloc(first.space, 0x401000, 0x1000, "rw")
expect(first.ok).to_equal(true)
expect(second.ok).to_equal(false)
expect(second.state).to_equal("fixed-map-conflict")
```

</details>

#### protects committed memory and returns old permissions

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val allocated = wine_nt_virtual_memory_alloc(wine_vm_space_new(), 0x500000, 0x1000, "rw")
val protected = wine_nt_virtual_memory_protect(allocated.space, 0x500000, "rx")
expect(protected.ok).to_equal(true)
expect(protected.state).to_equal("protected")
expect(protected.old_perms).to_equal("rw")
expect(wine_vm_access_gate(protected.space, 0x500000, "execute")).to_equal("ready")
expect(wine_vm_access_gate(protected.space, 0x500000, "write")).to_equal("page-fault-write")
```

</details>

#### frees mapped memory through the VM adapter

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val allocated = wine_nt_virtual_memory_alloc(wine_vm_space_new(), 0x600000, 0x1000, "rw")
val freed = wine_nt_virtual_memory_free(allocated.space, 0x600000)
expect(freed.ok).to_equal(true)
expect(freed.state).to_equal("freed")
expect(wine_vm_access_gate(freed.space, 0x600000, "read")).to_equal("page-fault-unmapped")
```

</details>

#### rejects invalid allocation and missing protect/free targets

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_nt_virtual_memory_alloc(wine_vm_space_new(), 0, 0, "rw").state).to_equal("invalid-size")
expect(wine_nt_virtual_memory_protect(wine_vm_space_new(), 0x700000, "rx").state).to_equal("missing-region")
expect(wine_nt_virtual_memory_free(wine_vm_space_new(), 0x700000).state).to_equal("missing-region")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_nt_virtual_memory_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine NT virtual memory bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
