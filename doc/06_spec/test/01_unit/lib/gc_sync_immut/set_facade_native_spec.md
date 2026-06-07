# Set Facade Native Specification

> <details>

<!-- sdn-diagram:id=set_facade_native_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=set_facade_native_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

set_facade_native_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=set_facade_native_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Set Facade Native Specification

## Scenarios

### gc_sync_immut PersistentSet native backend

#### adds and finds a root-facade entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = PersistentSet.empty()
val first = base.add("a")

expect(base.len()).to_equal(0)
expect(first.len()).to_equal(1)
expect(first.contains("a")).to_equal(true)
```

</details>

#### stores two root-facade entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first = PersistentSet.empty().add("a").add("b")

expect(first.len()).to_equal(2)
expect(first.contains("a")).to_equal(true)
expect(first.contains("b")).to_equal(true)
```

</details>

#### stores branch-shaped root-facade entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base: PersistentSet = PersistentSet.empty()
val first: PersistentSet = base.add("app").add("apple")

expect(first.len()).to_equal(2)
expect(first.contains("app")).to_equal(true)
expect(first.contains("apple")).to_equal(true)
```

</details>

#### deduplicates and removes branch-shaped root-facade entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base: PersistentSet = PersistentSet.empty()
val first: PersistentSet = base.add("app").add("apple").add("app")
val removed: PersistentSet = first.remove("apple")

expect(first.contains("app")).to_equal(true)
expect(first.contains("apple")).to_equal(true)
expect(first.len()).to_equal(2)
expect(removed.contains("app")).to_equal(true)
expect(removed.contains("apple")).to_equal(false)
expect(removed.len()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_sync_immut/set_facade_native_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_sync_immut PersistentSet native backend

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
