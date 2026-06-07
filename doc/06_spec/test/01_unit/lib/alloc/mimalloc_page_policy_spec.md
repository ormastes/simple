# Mimalloc Page Policy Specification

> BDD specs for cross-thread delayed free and page commit/decommit policy. Covers MiDelayedFreeList mechanics, MiPagePolicy state transitions, and the should_decommit predicate.

<!-- sdn-diagram:id=mimalloc_page_policy_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mimalloc_page_policy_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mimalloc_page_policy_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mimalloc_page_policy_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mimalloc Page Policy Specification

BDD specs for cross-thread delayed free and page commit/decommit policy. Covers MiDelayedFreeList mechanics, MiPagePolicy state transitions, and the should_decommit predicate.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #alloc-002 |
| Category | Infrastructure \| Stdlib |
| Difficulty | 2/5 |
| Status | Draft |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/lib/alloc/mimalloc_page_policy_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

BDD specs for cross-thread delayed free and page commit/decommit policy.
Covers MiDelayedFreeList mechanics, MiPagePolicy state transitions,
and the should_decommit predicate.

## Scenarios

### MiDelayedFreeList

#### delayed_free_list_new creates an empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list = delayed_free_list_new()
expect(list.entries.len()).to_equal(0)
```

</details>

#### delayed_free_push increases length by one

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list = delayed_free_list_new()
val entry = MiDelayedFreeEntry(heap_id: 1, block_size: 64, block_index: 0)
val list2 = delayed_free_push(list, entry)
expect(list2.entries.len()).to_equal(1)
```

</details>

#### delayed_free_push adds multiple entries in order

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list = delayed_free_list_new()
val e1 = MiDelayedFreeEntry(heap_id: 1, block_size: 32, block_index: 0)
val e2 = MiDelayedFreeEntry(heap_id: 2, block_size: 64, block_index: 1)
val list2 = delayed_free_push(list, e1)
val list3 = delayed_free_push(list2, e2)
expect(list3.entries.len()).to_equal(2)
```

</details>

#### delayed_free_drain returns all entries and empties the list

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list = delayed_free_list_new()
val e1 = MiDelayedFreeEntry(heap_id: 1, block_size: 32, block_index: 0)
val e2 = MiDelayedFreeEntry(heap_id: 2, block_size: 64, block_index: 1)
val list2 = delayed_free_push(delayed_free_push(list, e1), e2)
val result = delayed_free_drain(list2)
val empty_list = result[0]
val drained = result[1]
expect(empty_list.entries.len()).to_equal(0)
expect(drained.len()).to_equal(2)
```

</details>

#### delayed_free_drain on empty list returns empty list and empty entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list = delayed_free_list_new()
val result = delayed_free_drain(list)
val empty_list = result[0]
val drained = result[1]
expect(empty_list.entries.len()).to_equal(0)
expect(drained.len()).to_equal(0)
```

</details>

### MiPagePolicy

#### page_policy_new creates a committed policy with defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = page_policy_new()
expect(policy.committed).to_equal(true)
expect(policy.decommit_threshold).to_equal(4096)
expect(policy.recommit_count).to_equal(0)
```

</details>

#### mi_page_decommit sets committed to false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = page_policy_new()
val decommitted = mi_page_decommit(policy)
expect(decommitted.committed).to_equal(false)
```

</details>

#### mi_page_decommit preserves threshold and count

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = page_policy_new()
val decommitted = mi_page_decommit(policy)
expect(decommitted.decommit_threshold).to_equal(4096)
expect(decommitted.recommit_count).to_equal(0)
```

</details>

#### mi_page_recommit sets committed to true

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = page_policy_new()
val decommitted = mi_page_decommit(policy)
val recommitted = mi_page_recommit(decommitted)
expect(recommitted.committed).to_equal(true)
```

</details>

#### mi_page_recommit increments recommit_count

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = page_policy_new()
val decommitted = mi_page_decommit(policy)
val recommitted = mi_page_recommit(decommitted)
expect(recommitted.recommit_count).to_equal(1)
```

</details>

#### mi_page_recommit again increments recommit_count further

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = page_policy_new()
val r1 = mi_page_recommit(mi_page_decommit(policy))
val r2 = mi_page_recommit(mi_page_decommit(r1))
expect(r2.recommit_count).to_equal(2)
```

</details>

#### should_decommit returns true when committed and free_bytes >= threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = page_policy_new()
expect(should_decommit(policy, 4096)).to_equal(true)
expect(should_decommit(policy, 8192)).to_equal(true)
```

</details>

#### should_decommit returns false when free_bytes < threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = page_policy_new()
expect(should_decommit(policy, 4095)).to_equal(false)
expect(should_decommit(policy, 0)).to_equal(false)
```

</details>

#### should_decommit returns false when page is already decommitted

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = mi_page_decommit(page_policy_new())
expect(should_decommit(policy, 8192)).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
