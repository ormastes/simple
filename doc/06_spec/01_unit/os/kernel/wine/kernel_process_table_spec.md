# Kernel Process Table Specification

> <details>

<!-- sdn-diagram:id=kernel_process_table_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=kernel_process_table_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

kernel_process_table_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=kernel_process_table_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Kernel Process Table Specification

## Scenarios

### kernel_process_table — PID registry

### AC-1: process_table_alloc_pid — real PID allocation

#### AC-1: alloc_pid returns a positive non-zero PID

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pid = process_table_alloc_pid()
expect(pid).to_be_greater_than(0)
```

</details>

#### AC-1: consecutive alloc_pid calls return distinct PIDs

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pid1 = process_table_alloc_pid()
val pid2 = process_table_alloc_pid()
expect(pid1).to_be_greater_than(0)
expect(pid2).to_be_greater_than(0)
# PIDs must be distinct (no duplicate allocation)
expect(pid1 == pid2).to_equal(false)
```

</details>

#### AC-1: PID zero is reserved and never allocated

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The kernel convention: PID 0 = idle/swapper; never returned to userland
val pid = process_table_alloc_pid()
expect(pid == 0).to_equal(false)
```

</details>

### AC-1: process_table_register — process entry creation

#### AC-1: registered process is visible via lookup

1. process table register
   - Expected: entry.is_some is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pid = process_table_alloc_pid()
# asid=1 and a sentinel ns_id=42 represent a real ASID and namespace
process_table_register(pid, 1, 42)
val entry = process_table_lookup(pid)
expect(entry.is_some).to_equal(true)
```

</details>

#### AC-1: registered entry carries the correct PID

1. process table register
   - Expected: entry.is_some is true
   - Expected: entry.value.pid equals `pid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pid = process_table_alloc_pid()
process_table_register(pid, 2, 1)
val entry = process_table_lookup(pid)
expect(entry.is_some).to_equal(true)
expect(entry.value.pid).to_equal(pid)
```

</details>

#### AC-1: registered entry carries the supplied asid

1. process table register
   - Expected: entry.is_some is true
   - Expected: entry.value.asid equals `asid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pid = process_table_alloc_pid()
val asid: u64 = 7
process_table_register(pid, asid, 1)
val entry = process_table_lookup(pid)
expect(entry.is_some).to_equal(true)
expect(entry.value.asid).to_equal(asid)
```

</details>

#### AC-1: registered entry carries the supplied namespace ref

1. process table register
   - Expected: entry.is_some is true
   - Expected: entry.value.ns_id equals `ns_id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pid = process_table_alloc_pid()
val ns_id: u64 = 99
process_table_register(pid, 1, ns_id)
val entry = process_table_lookup(pid)
expect(entry.is_some).to_equal(true)
expect(entry.value.ns_id).to_equal(ns_id)
```

</details>

### AC-1: process_table_lookup — process query

#### AC-1: lookup of unregistered PID returns None

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# A large PID unlikely to be registered
val entry = process_table_lookup(65534)
expect(entry.is_some).to_equal(false)
```

</details>

#### AC-1: lookup returns Some after register and None after reap

1. process table register
   - Expected: before.is_some is true
2. process table reap
   - Expected: after.is_some is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pid = process_table_alloc_pid()
process_table_register(pid, 3, 1)
val before = process_table_lookup(pid)
expect(before.is_some).to_equal(true)
process_table_reap(pid)
val after = process_table_lookup(pid)
expect(after.is_some).to_equal(false)
```

</details>

### AC-1: process_table_reap — entry removal

#### AC-1: reap on a registered PID succeeds without error

1. process table register
2. process table reap
   - Expected: entry.is_some is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pid = process_table_alloc_pid()
process_table_register(pid, 4, 1)
# reap returns void; we verify by confirming lookup is None afterward
process_table_reap(pid)
val entry = process_table_lookup(pid)
expect(entry.is_some).to_equal(false)
```

</details>

#### AC-1: no resident fallback markers remain after reap

1. process table register
   - Expected: entry.is_some is true
   - Expected: entry.value.state equals `running`
2. process table reap
   - Expected: reaped.is_some is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Validates AC-1: apps launch with real PIDs, no fallback markers
val pid = process_table_alloc_pid()
expect(pid).to_be_greater_than(0)
process_table_register(pid, 5, 1)
val entry = process_table_lookup(pid)
expect(entry.is_some).to_equal(true)
expect(entry.value.state).to_equal("running")
process_table_reap(pid)
val reaped = process_table_lookup(pid)
expect(reaped.is_some).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/wine/kernel_process_table_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- kernel_process_table — PID registry
- AC-1: process_table_alloc_pid — real PID allocation
- AC-1: process_table_register — process entry creation
- AC-1: process_table_lookup — process query
- AC-1: process_table_reap — entry removal

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
