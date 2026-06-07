# Map Facade Native Specification

> <details>

<!-- sdn-diagram:id=map_facade_native_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=map_facade_native_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

map_facade_native_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=map_facade_native_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Map Facade Native Specification

## Scenarios

### nogc_sync_immut PersistentMap native backend

#### stores and retrieves a root-facade entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = PersistentMap.empty()
val first = base.set("a", 1)

expect(base.len()).to_equal(0)
expect(first.len()).to_equal(1)
expect(first.get("a")).to_equal(1)
```

</details>

#### stores two root-facade entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first = PersistentMap.empty().set("a", 1).set("b", 2)

expect(first.get("a")).to_equal(1)
expect(first.get("b")).to_equal(2)
expect(first.len()).to_equal(2)
```

</details>

#### stores branch-shaped root-facade entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base: PersistentMap = PersistentMap.empty()
val first: PersistentMap = base.set("app", 1).set("apple", 2)

expect(first.get("app")).to_equal(1)
expect(first.get("apple")).to_equal(2)
expect(first.len()).to_equal(2)
```

</details>

#### overwrites branch-shaped root-facade entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base: PersistentMap = PersistentMap.empty()
val first: PersistentMap = base.set("app", 1).set("apple", 2)
val overwritten: PersistentMap = first.set("app", 3)

expect(overwritten.get("app")).to_equal(3)
expect(overwritten.get("apple")).to_equal(2)
expect(overwritten.len()).to_equal(2)
```

</details>

#### removes branch-shaped root-facade entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base: PersistentMap = PersistentMap.empty()
val first: PersistentMap = base.set("app", 1).set("apple", 2)
val removed: PersistentMap = first.remove("apple")

expect(removed.get("app")).to_equal(1)
expect(removed.get("apple")).to_equal(nil)
expect(removed.len()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_immut/map_facade_native_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_sync_immut PersistentMap native backend

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
