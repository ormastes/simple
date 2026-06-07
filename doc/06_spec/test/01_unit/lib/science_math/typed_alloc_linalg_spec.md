# Typed Alloc Linalg Specification

> <details>

<!-- sdn-diagram:id=typed_alloc_linalg_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=typed_alloc_linalg_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

typed_alloc_linalg_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=typed_alloc_linalg_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Typed Alloc Linalg Specification

## Scenarios

### typed numeric allocation perf sugar

#### allocates zero-filled f64 buffers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = alloc_f64(4)
expect(arr.len()).to_equal(4)
expect(arr[0]).to_equal(0.0)
expect(arr[3]).to_equal(0.0)
```

</details>

#### allocates zero-filled f32 buffers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = alloc_f32(3)
expect(arr.len()).to_equal(3)
expect(arr[0]).to_equal(0.0f32)
expect(arr[2]).to_equal(0.0f32)
```

</details>

#### allocates zero-filled i64 buffers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = alloc_i64(3)
expect(arr.len()).to_equal(3)
expect(arr[0]).to_equal(0)
expect(arr[2]).to_equal(0)
```

</details>

#### allocates zero-filled i32 buffers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = alloc_i32(3)
expect(arr.len()).to_equal(3)
expect(arr[0]).to_equal(0)
expect(arr[2]).to_equal(0)
```

</details>

#### returns empty buffers for non-positive lengths

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alloc_f64(0).len()).to_equal(0)
expect(alloc_i64(-1).len()).to_equal(0)
```

</details>

### linalg typed allocation consumers

#### mat_zeros uses zero-filled f64 data

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = mat_zeros(2, 3)
expect(m.data.len()).to_equal(6)
expect(m.get(0, 0)).to_equal(0.0)
expect(m.get(1, 2)).to_equal(0.0)
```

</details>

#### mat_identity sets only diagonal entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = mat_identity(3)
expect(m.data.len()).to_equal(9)
expect(m.get(0, 0)).to_equal(1.0)
expect(m.get(1, 1)).to_equal(1.0)
expect(m.get(2, 2)).to_equal(1.0)
expect(m.get(0, 1)).to_equal(0.0)
expect(m.get(2, 1)).to_equal(0.0)
```

</details>

#### mat_mul writes into a preallocated f64 result buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = mat_identity(2)
val b = mat_identity(2)
val c = mat_mul(a, b)
expect(c.data.len()).to_equal(4)
expect(c.get(0, 0)).to_equal(1.0)
expect(c.get(0, 1)).to_equal(0.0)
expect(c.get(1, 0)).to_equal(0.0)
expect(c.get(1, 1)).to_equal(1.0)
```

</details>

#### mat_transpose writes into a preallocated f64 result buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = mat_zeros(2, 3)
val t = mat_transpose(m)
expect(t.data.len()).to_equal(6)
expect(t.rows).to_equal(3)
expect(t.cols).to_equal(2)
expect(t.get(2, 1)).to_equal(0.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/science_math/typed_alloc_linalg_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- typed numeric allocation perf sugar
- linalg typed allocation consumers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
