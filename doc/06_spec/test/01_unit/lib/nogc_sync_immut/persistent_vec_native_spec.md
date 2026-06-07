# Persistent Vec Native Specification

> <details>

<!-- sdn-diagram:id=persistent_vec_native_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=persistent_vec_native_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

persistent_vec_native_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=persistent_vec_native_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Persistent Vec Native Specification

## Scenarios

### nogc_sync_immut PersistentVec native backend

#### preserves repeated pushes and tail updates

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = PersistentVec.empty()
val one = base.push(10)
val two = one.push(20)
expect(base.len()).to_equal(0)
expect(one.len()).to_equal(1)
expect(one.get(0)).to_equal(10)
expect(two.len()).to_equal(2)
expect(two.get(0)).to_equal(10)
expect(two.get(1)).to_equal(20)

val three = two.push(30)
val changed = three.set(1, 99)
expect(three.get(1)).to_equal(20)
expect(changed.len()).to_equal(3)
expect(changed.get(0)).to_equal(10)
expect(changed.get(1)).to_equal(99)
expect(changed.get(2)).to_equal(30)

val sample = PersistentVec.from_array([4, 5, 6])
expect(sample.len()).to_equal(3)
expect(sample.get(0)).to_equal(4)
expect(sample.get(1)).to_equal(5)
expect(sample.get(2)).to_equal(6)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_immut/persistent_vec_native_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_sync_immut PersistentVec native backend

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
