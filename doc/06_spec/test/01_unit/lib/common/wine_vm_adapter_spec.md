# Wine Vm Adapter Specification

> <details>

<!-- sdn-diagram:id=wine_vm_adapter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_vm_adapter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_vm_adapter_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_vm_adapter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Vm Adapter Specification

## Scenarios

### Wine VM adapter model

#### detects interval overlap for fixed mappings

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_vm_regions_overlap(100, 20, 110, 20)).to_equal(true)
expect(wine_vm_regions_overlap(100, 20, 120, 20)).to_equal(false)
```

</details>

#### reserves automatic and fixed ranges

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val auto_res = wine_vm_reserve(wine_vm_space_new(), 0x2000)
expect(auto_res.ok).to_equal(true)
expect(auto_res.region.base).to_equal(0x10000000)

val fixed = wine_vm_reserve_fixed(auto_res.space, 0x20000000, 0x1000)
expect(fixed.ok).to_equal(true)
expect(fixed.region.base).to_equal(0x20000000)
```

</details>

#### rejects overlapping fixed mappings

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first = wine_vm_reserve_fixed(wine_vm_space_new(), 0x400000, 0x2000)
val second = wine_vm_reserve_fixed(first.space, 0x401000, 0x2000)
expect(second.ok).to_equal(false)
expect(second.state).to_equal("fixed-map-conflict")
```

</details>

#### commits and protects reserved regions

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reserved = wine_vm_reserve_fixed(wine_vm_space_new(), 0x500000, 0x1000)
val committed = wine_vm_commit(reserved.space, 0x500000, "rw")
expect(committed.state).to_equal("committed")
val protected = wine_vm_protect(committed.space, 0x500000, "rx")
expect(protected.state).to_equal("protected")
expect(wine_vm_access_gate(protected.space, 0x500000, "execute")).to_equal("ready")
expect(wine_vm_access_gate(protected.space, 0x500000, "write")).to_equal("page-fault-write")
```

</details>

#### writes and reads modeled bytes from committed writable VM memory

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reserved = wine_vm_reserve_fixed(wine_vm_space_new(), 0x510000, 0x1000)
val committed = wine_vm_commit(reserved.space, 0x510000, "rw")
val written = wine_vm_write_bytes(committed.space, 0x510008, [1, 2, 3, 4])
expect(written.ok).to_equal(true)
expect(written.operations).to_equal("VMBytesWritten")

val read = wine_vm_read_bytes(written.space, 0x510008, 4)
expect(read.ok).to_equal(true)
expect(read.operations).to_equal("VMBytesRead")
expect(read.bytes[0]).to_equal(1)
expect(read.bytes[3]).to_equal(4)
```

</details>

#### rejects modeled byte writes that cross region bounds or write-protected pages

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reserved = wine_vm_reserve_fixed(wine_vm_space_new(), 0x520000, 0x10)
val committed = wine_vm_commit(reserved.space, 0x520000, "r")
val protected = wine_vm_write_bytes(committed.space, 0x520000, [1])
expect(protected.ok).to_equal(false)
expect(protected.state).to_equal("page-fault-write")

val rw = wine_vm_protect(committed.space, 0x520000, "rw")
val boundary = wine_vm_write_bytes(rw.space, 0x52000f, [1, 2])
expect(boundary.ok).to_equal(false)
expect(boundary.state).to_equal("page-fault-boundary")
```

</details>

#### reports guard and uncommitted faults

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reserved = wine_vm_reserve_fixed(wine_vm_space_new(), 0x600000, 0x1000)
expect(wine_vm_access_gate(reserved.space, 0x600000, "read")).to_equal("page-fault-uncommitted")
val committed = wine_vm_commit(reserved.space, 0x600000, "rw")
val guarded = wine_vm_mark_guard(committed.space, 0x600000)
expect(wine_vm_access_gate(guarded.space, 0x600000, "read")).to_equal("page-fault-guard")
```

</details>

#### unmaps regions and validates user pointer lookup

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reserved = wine_vm_reserve_fixed(wine_vm_space_new(), 0x700000, 0x1000)
expect(wine_vm_region_contains(wine_vm_space_find(reserved.space, 0x700100), 0x700100)).to_equal(true)
val unmapped = wine_vm_unmap(reserved.space, 0x700000)
expect(unmapped.state).to_equal("unmapped")
expect(wine_vm_access_gate(unmapped.space, 0x700100, "read")).to_equal("page-fault-unmapped")
```

</details>

#### builds fault evidence accepted by the VM fault gate

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = wine_vm_fault_evidence(_fault())
expect(evidence).to_contain("process=10")
expect(evidence).to_contain("thread=20")
expect(evidence).to_contain("policy=deliver-seh")
```

</details>

#### derives ready VM features when mappings, guard, exec, namespaces, and fault evidence exist

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reserved = wine_vm_reserve_fixed(wine_vm_space_new(), 0x800000, 0x1000)
val committed = wine_vm_commit(reserved.space, 0x800000, "rx")
val guarded = wine_vm_mark_guard(committed.space, 0x800000)
val container = "pid fs ipc net capability"
val features = wine_vm_adapter_feature_string(guarded.space, container)
expect(features).to_contain("exec-perm")
expect(features).to_contain("guard-page")
expect(features).to_contain("cap-namespace")
expect(wine_vm_adapter_gate(guarded.space, container, _fault())).to_equal("ready")
```

</details>

#### does not derive namespace features from container substring collisions

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reserved = wine_vm_reserve_fixed(wine_vm_space_new(), 0x810000, 0x1000)
val committed = wine_vm_commit(reserved.space, 0x810000, "rx")
val guarded = wine_vm_mark_guard(committed.space, 0x810000)
val container = "stupid xfs epic ethernet incapability"
val features = wine_vm_adapter_feature_string(guarded.space, container)
expect(features.contains("pid-namespace")).to_equal(false)
expect(features.contains("fs-namespace")).to_equal(false)
expect(features.contains("ipc-namespace")).to_equal(false)
expect(features.contains("net-namespace")).to_equal(false)
expect(features.contains("cap-namespace")).to_equal(false)
expect(wine_vm_adapter_gate(guarded.space, container, _fault())).to_equal("missing-pid-namespace")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_vm_adapter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine VM adapter model

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
