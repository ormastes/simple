# Heap Mimalloc Specification

> <details>

<!-- sdn-diagram:id=heap_mimalloc_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=heap_mimalloc_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

heap_mimalloc_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=heap_mimalloc_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Heap Mimalloc Specification

## Scenarios

### SimpleOS mimalloc kernel heap boundary

#### starts with zero tracked allocation state

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(heap_total_allocated()).to_equal(0)
expect(heap_total_free()).to_equal(0)
expect(heap_alloc_count()).to_equal(0)
```

</details>

#### passes integrity check before boot heap initialization

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(heap_integrity_check()).to_equal(true)
```

</details>

#### rejects zero-byte allocation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ptr = heap_alloc(0)
expect(ptr.?).to_equal(false)
```

</details>

#### returns nil before the mimalloc OS page provider has a bump region

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ptr = heap_alloc(64)
expect(ptr.?).to_equal(false)
expect(heap_alloc_count()).to_equal(0)
```

</details>

#### ignores null frees

1. heap free
   - Expected: heap_alloc_count() equals `0`
   - Expected: heap_integrity_check() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
heap_free(VirtAddr(addr: 0))
expect(heap_alloc_count()).to_equal(0)
expect(heap_integrity_check()).to_equal(true)
```

</details>

#### ignores null sized frees

1. heap free size
   - Expected: heap_alloc_count() equals `0`
   - Expected: heap_integrity_check() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
heap_free_size(VirtAddr(addr: 0), 64)
expect(heap_alloc_count()).to_equal(0)
expect(heap_integrity_check()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/memory/heap_mimalloc_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS mimalloc kernel heap boundary

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
