# Process Isolation As Specification

> 1. expect as phys root

<!-- sdn-diagram:id=process_isolation_as_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=process_isolation_as_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

process_isolation_as_spec -> std
process_isolation_as_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=process_isolation_as_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Process Isolation As Specification

## Scenarios

### AddressSpace handle accessors

#### as_phys_root returns the physical root

1. expect as phys root


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val space = AddressSpace(phys_root: 0x1000, id: 7)
expect as_phys_root(space) == 0x1000
```

</details>

#### as_id returns the monotonic id

1. expect as id


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val space = AddressSpace(phys_root: 0x2000, id: 42)
expect as_id(space) == 42
```

</details>

#### as_is_kernel true for zero root

1. expect as is kernel


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val space = AddressSpace(phys_root: 0, id: 0)
expect as_is_kernel(space) == true
```

</details>

#### as_is_kernel false for nonzero root

1. expect as is kernel


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val space = AddressSpace(phys_root: 0x3000, id: 1)
expect as_is_kernel(space) == false
```

</details>

#### as_kernel_sentinel returns zero root

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sentinel = as_kernel_sentinel()
expect sentinel.phys_root == 0
expect sentinel.id == 0
```

</details>

### as_switch_to deduplication

#### as_switch_to updates current root

1. as switch to
2. expect as current phys root


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
as_switch_to(0x4000)
expect as_current_phys_root() == 0x4000
```

</details>

#### as_switch_to is idempotent (same root twice)

1. as switch to
2. as switch to
3. expect as current phys root


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
as_switch_to(0x5000)
as_switch_to(0x5000)
expect as_current_phys_root() == 0x5000
```

</details>

#### as_switch_to zero root is a no-op after the root is set

1. as switch to
2. as switch to
3. expect as current phys root


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
as_switch_to(0x6000)
as_switch_to(0)
# zero means no-op; current root stays from previous call
expect as_current_phys_root() == 0x6000
```

</details>

### as_create / as_destroy lifecycle

#### as_create returns an AddressSpace (phys_root may be 1 if VMM not init)

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val space = as_create()
val root = as_phys_root(space)
expect (root == 0 or root == 1 or root > 4096) == true
```

</details>

#### as_destroy on kernel sentinel is a no-op

1. as destroy
2. expect as phys root


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sentinel = as_kernel_sentinel()
as_destroy(sentinel)
expect as_phys_root(sentinel) == 0
```

</details>

#### as_destroy on sentinel root=1 is a no-op

1. as destroy
2. expect as phys root


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val legacy = AddressSpace(phys_root: 1, id: 0)
as_destroy(legacy)
expect as_phys_root(legacy) == 1
```

</details>

### Process Table Extended — alloc and register

#### pt_ext_alloc_pid is monotonically increasing

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p1 = pt_ext_alloc_pid()
val p2 = pt_ext_alloc_pid()
expect p2 > p1
```

</details>

#### pt_ext_alloc_pid always > 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pid = pt_ext_alloc_pid()
expect pid > 0
```

</details>

#### pt_ext_register + pt_ext_lookup round-trip

1. pt ext register


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pid = pt_ext_alloc_pid()
val space = AddressSpace(phys_root: 0x9000, id: 99)
pt_ext_register(pid, space)
val opt = pt_ext_lookup(pid)
expect opt.is_some == true
expect opt.entry.pid == pid
expect opt.entry.space.phys_root == 0x9000
```

</details>

#### pt_ext_lookup absent PID returns is_some = false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = pt_ext_lookup(-999)
expect opt.is_some == false
```

</details>

#### pt_ext_set_state updates state field

1. pt ext register
2. pt ext set state


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pid = pt_ext_alloc_pid()
val space = AddressSpace(phys_root: 0xA000, id: 3)
pt_ext_register(pid, space)
pt_ext_set_state(pid, "blocked")
val opt = pt_ext_lookup(pid)
expect opt.is_some == true
expect opt.entry.state == "blocked"
```

</details>

#### pt_ext_reap tombstones the entry

1. pt ext register
2. pt ext reap


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pid = pt_ext_alloc_pid()
val space = AddressSpace(phys_root: 1, id: 0)
pt_ext_register(pid, space)
pt_ext_reap(pid)
val opt = pt_ext_lookup(pid)
expect opt.is_some == false
```

</details>

### Process Table Extended — count and list

#### pt_ext_count increases after register

1. pt ext register


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = pt_ext_count()
val pid = pt_ext_alloc_pid()
pt_ext_register(pid, AddressSpace(phys_root: 1, id: 0))
val after = pt_ext_count()
expect after == before + 1
```

</details>

#### pt_ext_list_pids contains newly registered pid

1. pt ext register


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pid = pt_ext_alloc_pid()
pt_ext_register(pid, AddressSpace(phys_root: 1, id: 0))
val pids = pt_ext_list_pids()
var found = false
var i = 0
while i < pids.len():
    if pids[i] == pid:
        found = true
    i = i + 1
expect found == true
```

</details>

### Convenience helpers

#### pt_ext_spawn returns a positive pid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pid = pt_ext_spawn()
expect pid > 0
```

</details>

#### pt_ext_spawn registers a live entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pid = pt_ext_spawn()
val opt = pt_ext_lookup(pid)
expect opt.is_some == true
```

</details>

#### pt_ext_spawn_with_kernel_as registers with phys_root 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pid = pt_ext_spawn_with_kernel_as()
val opt = pt_ext_lookup(pid)
expect opt.is_some == true
expect opt.entry.space.phys_root == 0
```

</details>

#### pt_ext_address_space_for returns sentinel for unknown pid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val space = pt_ext_address_space_for(-777)
expect space.phys_root == 0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/process_isolation_as_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AddressSpace handle accessors
- as_switch_to deduplication
- as_create / as_destroy lifecycle
- Process Table Extended — alloc and register
- Process Table Extended — count and list
- Convenience helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
