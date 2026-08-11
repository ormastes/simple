# Db Accel Index Specification

> <details>

<!-- sdn-diagram:id=db_accel_index_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=db_accel_index_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

db_accel_index_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=db_accel_index_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Db Accel Index Specification

## Scenarios

### PrefixIndex

#### starts empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = prefix_index_new()
expect(prefix_index_size(idx)).to_equal(0)
```

</details>

#### insert increases size

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = prefix_index_new()
val idx2 = prefix_index_insert(idx, "ns/foo", 1)
expect(prefix_index_size(idx2)).to_equal(1)
```

</details>

#### lookup prefix finds matching entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = prefix_index_new()
val idx2 = prefix_index_insert(idx, "ns/foo", 10)
val idx3 = prefix_index_insert(idx2, "ns/bar", 20)
val hits = prefix_index_lookup_prefix(idx3, "ns/")
expect(hits.len()).to_equal(2)
```

</details>

#### lookup prefix excludes non-matching entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = prefix_index_new()
val idx2 = prefix_index_insert(idx, "ns/foo", 10)
val idx3 = prefix_index_insert(idx2, "other/baz", 30)
val hits = prefix_index_lookup_prefix(idx3, "ns/")
expect(hits.len()).to_equal(1)
```

</details>

#### lookup exact returns only exact match

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = prefix_index_new()
val idx2 = prefix_index_insert(idx, "ns/foo", 10)
val idx3 = prefix_index_insert(idx2, "ns/foobar", 20)
val hits = prefix_index_lookup_exact(idx3, "ns/foo")
expect(hits.len()).to_equal(1)
```

</details>

### TextIndex

#### starts empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tidx = text_index_new()
expect(text_index_size(tidx)).to_equal(0)
```

</details>

#### insert grows size

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tidx = text_index_new()
val tidx2 = text_index_insert(tidx, "hello world", 0)
expect(text_index_size(tidx2)).to_equal(1)
```

</details>

#### search_prefix finds entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tidx = text_index_new()
val tidx2 = text_index_insert(tidx, "user/alice", 0)
val tidx3 = text_index_insert(tidx2, "user/bob", 1)
val tidx4 = text_index_insert(tidx3, "admin/carol", 2)
expect(text_index_count_prefix(tidx4, "user/")).to_equal(2)
```

</details>

#### search_contains finds substring

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tidx = text_index_new()
val tidx2 = text_index_insert(tidx, "hello world", 0)
val tidx3 = text_index_insert(tidx2, "goodbye world", 1)
val tidx4 = text_index_insert(tidx3, "nothing here", 2)
expect(text_index_count_contains(tidx4, "world")).to_equal(2)
```

</details>

#### search_exact returns only exact match

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tidx = text_index_new()
val tidx2 = text_index_insert(tidx, "foo", 0)
val tidx3 = text_index_insert(tidx2, "foobar", 1)
val hits = text_index_search_exact(tidx3, "foo")
expect(hits.len()).to_equal(1)
```

</details>

#### search_contains empty token matches all

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tidx = text_index_new()
val tidx2 = text_index_insert(tidx, "alpha", 0)
val tidx3 = text_index_insert(tidx2, "beta", 1)
expect(text_index_count_contains(tidx3, "")).to_equal(2)
```

</details>

### PageSummary

#### scan_range returns pages overlapping range

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = page_summary_index_new()
val p0 = page_summary_new(0, 1, 100, 50)
val p1 = page_summary_new(1, 101, 200, 50)
val idx2 = page_summary_index_add(idx, p0)
val idx3 = page_summary_index_add(idx2, p1)
val hits = page_summary_scan_range(idx3, 50, 150)
expect(hits.len()).to_equal(2)
```

</details>

#### scan_range excludes non-overlapping pages

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = page_summary_index_new()
val p0 = page_summary_new(0, 1, 100, 50)
val p1 = page_summary_new(1, 101, 200, 50)
val idx2 = page_summary_index_add(idx, p0)
val idx3 = page_summary_index_add(idx2, p1)
val hits = page_summary_scan_range(idx3, 150, 200)
expect(hits.len()).to_equal(1)
```

</details>

#### total_rows sums all pages

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = page_summary_index_new()
val p0 = page_summary_new(0, 1, 100, 30)
val p1 = page_summary_new(1, 101, 200, 20)
val idx2 = page_summary_index_add(idx, p0)
val idx3 = page_summary_index_add(idx2, p1)
expect(page_summary_total_rows(idx3)).to_equal(50)
```

</details>

#### hash is deterministic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h1 = page_summary_hash(1, 100, 50)
val h2 = page_summary_hash(1, 100, 50)
expect(h1).to_equal(h2)
```

</details>

#### hash differs for different inputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h1 = page_summary_hash(1, 100, 50)
val h2 = page_summary_hash(1, 200, 50)
expect((h1 == h2) == false).to_equal(true)
```

</details>

### FilterIn

#### filter_in_text matches all needles present

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = ["a", "b", "c", "d"]
val needles = ["b", "d"]
val result = filter_in_text(values, needles)
expect(result.matched_count).to_equal(2)
```

</details>

#### filter_in_text empty needles matches nothing

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = ["a", "b", "c"]
val needles: [text] = []
val result = filter_in_text(values, needles)
expect(result.matched_count).to_equal(0)
```

</details>

#### filter_in_int OR semantics returns correct row ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = [10, 20, 30, 40, 50]
val needles = [20, 40]
val result = filter_in_int(values, needles)
expect(result.row_ids.len()).to_equal(2)
```

</details>

#### filter_in_int_count helper is consistent

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = [1, 2, 3, 4, 5]
val needles = [1, 3, 5]
expect(filter_in_int_count(values, needles)).to_equal(3)
```

</details>

#### filter_in_text_count helper is consistent

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = ["x", "y", "z"]
val needles = ["x", "z"]
expect(filter_in_text_count(values, needles)).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/bench/db_accel_index/db_accel_index_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- PrefixIndex
- TextIndex
- PageSummary
- FilterIn

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
