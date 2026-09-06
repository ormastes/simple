# Compute Algo Ext Specification

> <details>

<!-- sdn-diagram:id=compute_algo_ext_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compute_algo_ext_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compute_algo_ext_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compute_algo_ext_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compute Algo Ext Specification

## Scenarios

### compute_algo_ext

#### min_element returns index of minimum

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = cpu_target()
val data = [5, 2, 8, 1, 9]
expect(compute_min_element(data, less_i64, t)).to_equal(3)
```

</details>

#### min_element returns -1 on empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = cpu_target()
val data: [i64] = []
expect(compute_min_element(data, less_i64, t)).to_equal(-1)
```

</details>

#### max_element returns index of maximum

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = cpu_target()
val data = [5, 2, 8, 1, 9]
expect(compute_max_element(data, less_i64, t)).to_equal(4)
```

</details>

#### max_element returns -1 on empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = cpu_target()
val data: [i64] = []
expect(compute_max_element(data, less_i64, t)).to_equal(-1)
```

</details>

#### transform_reduce doubles then sums

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = cpu_target()
val data = [1, 2, 3, 4]
# (2+4+6+8) + init 0 = 20
expect(compute_transform_reduce(data, dbl_i64, 0, add_i64, t)).to_equal(20)
```

</details>

#### transform_reduce on empty returns init

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = cpu_target()
val data: [i64] = []
expect(compute_transform_reduce(data, dbl_i64, 7, add_i64, t)).to_equal(7)
```

</details>

#### unique removes consecutive duplicates

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = cpu_target()
val data = [1, 1, 2, 3, 3, 3, 1]
val out = compute_unique(data, eq_i64, t)
expect(out.len()).to_equal(4)
expect(out[0]).to_equal(1)
expect(out[1]).to_equal(2)
expect(out[2]).to_equal(3)
expect(out[3]).to_equal(1)
```

</details>

#### unique on empty returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = cpu_target()
val data: [i64] = []
val out = compute_unique(data, eq_i64, t)
expect(out.len()).to_equal(0)
```

</details>

#### lower_bound finds first not-less index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = cpu_target()
val data = [1, 3, 5, 7]
expect(compute_lower_bound(data, 5, less_i64, t)).to_equal(2)
```

</details>

#### lower_bound of missing low key is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = cpu_target()
val data = [1, 3, 5, 7]
expect(compute_lower_bound(data, 0, less_i64, t)).to_equal(0)
```

</details>

#### lower_bound of key above all is len

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = cpu_target()
val data = [1, 3, 5, 7]
expect(compute_lower_bound(data, 9, less_i64, t)).to_equal(4)
```

</details>

#### binary_search hit

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = cpu_target()
val data = [1, 3, 5, 7]
expect(compute_binary_search(data, 5, less_i64, t)).to_equal(true)
```

</details>

#### binary_search miss

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = cpu_target()
val data = [1, 3, 5, 7]
expect(compute_binary_search(data, 4, less_i64, t)).to_equal(false)
```

</details>

#### binary_search on empty is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = cpu_target()
val data: [i64] = []
expect(compute_binary_search(data, 1, less_i64, t)).to_equal(false)
```

</details>

#### exclusive_scan prefixes from init

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = cpu_target()
val data = [1, 2, 3, 4]
val out = compute_exclusive_scan(data, 0, add_i64, t)
expect(out.len()).to_equal(4)
expect(out[0]).to_equal(0)
expect(out[1]).to_equal(1)
expect(out[2]).to_equal(3)
expect(out[3]).to_equal(6)
```

</details>

#### exclusive_scan on empty returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = cpu_target()
val data: [i64] = []
val out = compute_exclusive_scan(data, 5, add_i64, t)
expect(out.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/compute/compute_algo_ext_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- compute_algo_ext

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
