# Kernel Namespace Specification

> <details>

<!-- sdn-diagram:id=kernel_namespace_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=kernel_namespace_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

kernel_namespace_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=kernel_namespace_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Kernel Namespace Specification

## Scenarios

### kernel_namespace — isolation facets

### AC-4: NsFlags — namespace type constants

#### AC-4: NsFlags.pid is defined as a non-zero value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(NsFlags.pid).to_be_greater_than(0)
```

</details>

#### AC-4: NsFlags.fs is defined as a non-zero value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(NsFlags.fs).to_be_greater_than(0)
```

</details>

#### AC-4: NsFlags.ipc is defined as a non-zero value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(NsFlags.ipc).to_be_greater_than(0)
```

</details>

#### AC-4: NsFlags.net is defined as a non-zero value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(NsFlags.net).to_be_greater_than(0)
```

</details>

#### AC-4: NsFlags.capability is defined as a non-zero value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(NsFlags.capability).to_be_greater_than(0)
```

</details>

#### AC-4: NsFlags values are all distinct (no aliasing)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(NsFlags.pid == NsFlags.fs).to_equal(false)
expect(NsFlags.pid == NsFlags.ipc).to_equal(false)
expect(NsFlags.pid == NsFlags.net).to_equal(false)
expect(NsFlags.pid == NsFlags.capability).to_equal(false)
expect(NsFlags.fs == NsFlags.ipc).to_equal(false)
expect(NsFlags.fs == NsFlags.net).to_equal(false)
expect(NsFlags.net == NsFlags.capability).to_equal(false)
```

</details>

### AC-4: namespace_create — initial namespace

#### AC-4: namespace_create returns a positive ns_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ns_id = namespace_create(NsFlags.pid)
expect(ns_id).to_be_greater_than(0)
```

</details>

#### AC-4: namespace_create for each facet type succeeds

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ns_pid = namespace_create(NsFlags.pid)
val ns_fs  = namespace_create(NsFlags.fs)
val ns_ipc = namespace_create(NsFlags.ipc)
val ns_net = namespace_create(NsFlags.net)
val ns_cap = namespace_create(NsFlags.capability)
expect(ns_pid).to_be_greater_than(0)
expect(ns_fs).to_be_greater_than(0)
expect(ns_ipc).to_be_greater_than(0)
expect(ns_net).to_be_greater_than(0)
expect(ns_cap).to_be_greater_than(0)
```

</details>

#### AC-4: consecutive namespace_create calls return distinct ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = namespace_create(NsFlags.pid)
val b = namespace_create(NsFlags.pid)
expect(a == b).to_equal(false)
```

</details>

### AC-4: namespace_clone — isolation via clone

#### AC-4: namespace_clone returns a distinct id from the source

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parent = namespace_create(NsFlags.pid)
val child  = namespace_clone(parent, NsFlags.pid)
expect(child).to_be_greater_than(0)
expect(child == parent).to_equal(false)
```

</details>

#### AC-4: cloned namespace is independently visible via lookup

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parent = namespace_create(NsFlags.net)
val child  = namespace_clone(parent, NsFlags.net)
val entry  = namespace_lookup(child)
expect(entry.is_some).to_equal(true)
```

</details>

#### AC-4: dropping the parent does not invalidate the clone

1. namespace drop
   - Expected: entry.is_some is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parent = namespace_create(NsFlags.ipc)
val child  = namespace_clone(parent, NsFlags.ipc)
namespace_drop(parent)
val entry = namespace_lookup(child)
expect(entry.is_some).to_equal(true)
```

</details>

### AC-4: namespace_unshare — capability isolation

#### AC-4: namespace_unshare for capability creates a new restricted namespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = namespace_create(NsFlags.capability)
val restricted = namespace_unshare(original, NsFlags.capability)
expect(restricted).to_be_greater_than(0)
expect(restricted == original).to_equal(false)
```

</details>

#### AC-4: unshared capability namespace is visible via lookup

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original   = namespace_create(NsFlags.capability)
val restricted = namespace_unshare(original, NsFlags.capability)
val entry = namespace_lookup(restricted)
expect(entry.is_some).to_equal(true)
expect(entry.value.flags).to_equal(NsFlags.capability)
```

</details>

### AC-4: namespace_lookup — query

#### AC-4: lookup of unknown ns_id returns None

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = namespace_lookup(0xFFFFFFFF)
expect(entry.is_some).to_equal(false)
```

</details>

#### AC-4: lookup after drop returns None

1. namespace drop
   - Expected: entry.is_some is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ns_id = namespace_create(NsFlags.fs)
namespace_drop(ns_id)
val entry = namespace_lookup(ns_id)
expect(entry.is_some).to_equal(false)
```

</details>

### AC-4: container namespace — combined facets

#### AC-4: all five facet namespaces can be created for a single container

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Simulate the namespace set for a Wine/Proton container
val pid_ns = namespace_create(NsFlags.pid)
val fs_ns  = namespace_create(NsFlags.fs)
val ipc_ns = namespace_create(NsFlags.ipc)
val net_ns = namespace_create(NsFlags.net)
val cap_ns = namespace_create(NsFlags.capability)
expect(pid_ns).to_be_greater_than(0)
expect(fs_ns).to_be_greater_than(0)
expect(ipc_ns).to_be_greater_than(0)
expect(net_ns).to_be_greater_than(0)
expect(cap_ns).to_be_greater_than(0)
# All must be distinct
expect(pid_ns == fs_ns).to_equal(false)
expect(fs_ns == ipc_ns).to_equal(false)
expect(ipc_ns == net_ns).to_equal(false)
expect(net_ns == cap_ns).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/wine/kernel_namespace_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- kernel_namespace — isolation facets
- AC-4: NsFlags — namespace type constants
- AC-4: namespace_create — initial namespace
- AC-4: namespace_clone — isolation via clone
- AC-4: namespace_unshare — capability isolation
- AC-4: namespace_lookup — query
- AC-4: container namespace — combined facets

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
