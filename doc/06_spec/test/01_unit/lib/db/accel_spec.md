# Accel Specification

> 1. lhs set

<!-- sdn-diagram:id=accel_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=accel_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

accel_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=accel_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Accel Specification

## Scenarios

### DB accel — bitmap operations

#### preserves counts across and/or/and_not

1. lhs set
2. lhs set
3. lhs set
4. rhs set
5. rhs set
6. rhs set
   - Expected: both.count() equals `2`
   - Expected: either.count() equals `4`
   - Expected: only_lhs.count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lhs = RowBitmap.empty(8)
lhs.set(1)
lhs.set(3)
lhs.set(5)
val rhs = RowBitmap.empty(8)
rhs.set(3)
rhs.set(4)
rhs.set(5)

val both = lhs.and_with(rhs)
val either = lhs.or_with(rhs)
val only_lhs = lhs.and_not(rhs)

expect(both.count()).to_equal(2)
expect(either.count()).to_equal(4)
expect(only_lhs.count()).to_equal(1)
```

</details>

#### supports full, get, and clear across 31/32 and 63/64 boundaries

1. bitmap clear
2. bitmap clear
3. bitmap clear
4. bitmap clear
   - Expected: bitmap.get(0) is false
   - Expected: bitmap.get(1) is true
   - Expected: bitmap.get(31) is false
   - Expected: bitmap.get(32) is false
   - Expected: bitmap.get(64) is false
   - Expected: bitmap.count() equals `61`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bitmap = RowBitmap.full(65)
expect(bitmap.count()).to_equal(65)
expect(bitmap.get(0)).to_equal(true)
expect(bitmap.get(31)).to_equal(true)
expect(bitmap.get(32)).to_equal(true)
expect(bitmap.get(64)).to_equal(true)
expect(bitmap.get(65)).to_equal(false)

bitmap.clear(0)
bitmap.clear(31)
bitmap.clear(32)
bitmap.clear(64)
expect(bitmap.get(0)).to_equal(false)
expect(bitmap.get(1)).to_equal(true)
expect(bitmap.get(31)).to_equal(false)
expect(bitmap.get(32)).to_equal(false)
expect(bitmap.get(64)).to_equal(false)
expect(bitmap.count()).to_equal(61)
```

</details>

#### keeps and/or parity across mixed 31/32/63/64 boundaries

1. lhs set
2. lhs set
3. lhs set
4. lhs set
5. lhs set
6. lhs set
7. rhs set
8. rhs set
9. rhs set
10. rhs set
11. rhs set
   - Expected: both.row_count equals `70`
   - Expected: both.count() equals `4`
   - Expected: both.get(0) is true
   - Expected: both.get(31) is false
   - Expected: both.get(32) is true
   - Expected: both.get(62) is false
   - Expected: both.get(63) is true
   - Expected: both.get(64) is true
   - Expected: both.get(95) is false
   - Expected: either.row_count equals `96`
   - Expected: either.count() equals `7`
   - Expected: either.get(0) is true
   - Expected: either.get(31) is true
   - Expected: either.get(32) is true
   - Expected: either.get(62) is true
   - Expected: either.get(63) is true
   - Expected: either.get(64) is true
   - Expected: either.get(95) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lhs = RowBitmap.empty(96)
lhs.set(0)
lhs.set(31)
lhs.set(32)
lhs.set(63)
lhs.set(64)
lhs.set(95)

val rhs = RowBitmap.empty(70)
rhs.set(0)
rhs.set(32)
rhs.set(62)
rhs.set(63)
rhs.set(64)

val both = lhs.and_with(rhs)
val either = lhs.or_with(rhs)

expect(both.row_count).to_equal(70)
expect(both.count()).to_equal(4)
expect(both.get(0)).to_equal(true)
expect(both.get(31)).to_equal(false)
expect(both.get(32)).to_equal(true)
expect(both.get(62)).to_equal(false)
expect(both.get(63)).to_equal(true)
expect(both.get(64)).to_equal(true)
expect(both.get(95)).to_equal(false)

expect(either.row_count).to_equal(96)
expect(either.count()).to_equal(7)
expect(either.get(0)).to_equal(true)
expect(either.get(31)).to_equal(true)
expect(either.get(32)).to_equal(true)
expect(either.get(62)).to_equal(true)
expect(either.get(63)).to_equal(true)
expect(either.get(64)).to_equal(true)
expect(either.get(95)).to_equal(true)
```

</details>

### DB accel — text predicates

#### matches prefix and token boundaries

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_starts_with_span("alpha beta", "alpha")).to_equal(true)
expect(text_contains_token("alpha|beta,gamma", "beta")).to_equal(true)
expect(text_contains_token("alphabet soup", "alpha")).to_equal(false)
```

</details>

#### finds shared delimiter boundaries in bytes and text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val span = make_byte_span([("a" as u8), ("|" as u8), ("b" as u8)], 0, 3)
expect(byte_span_find_delimiter(span)).to_equal(1)
expect(text_find_delimiter("path,tail")).to_equal(4)
```

</details>

#### extracts trigrams and overlap

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val trigrams = trigram_extract("token")
expect(trigrams.len()).to_equal(3)
expect(trigram_overlap_count("token", "stokenized")).to_be_greater_than(0)
```

</details>

### DB accel — batched scalar scans

#### scans keys with identical scalar and bitmap counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val span = make_key_span([10, 20, 30, 20, 50], 0, 5)
val predicate = ScanPredicate(kind: ScanPredicateKind.Eq, text_value: "", key_value: 20)
val (bitmap, stats) = scan_key_span(span, predicate)
expect(bitmap.count()).to_equal(2)
expect(stats.candidates_kept).to_equal(2)
expect(stats.rows_scanned).to_equal(5)
```

</details>

#### scans text values for contains

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val predicate = ScanPredicate(kind: ScanPredicateKind.Contains, text_value: "src", key_value: 0)
val (bitmap, stats) = scan_text_values(["src/main.spl", "doc/readme.md", "src/lib.spl"], predicate)
expect(bitmap.count()).to_equal(2)
expect(stats.bitmap_density).to_be_greater_than(0.5)
```

</details>

#### collects row indices without bitmap materialization

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val predicate = ScanPredicate(kind: ScanPredicateKind.ContainsToken, text_value: "beta", key_value: 0)
val (rows, stats) = collect_text_row_indices(
    ["alpha|beta,gamma", "alpha beta", "beta", "betamax"],
    predicate
)
expect(rows.len()).to_equal(3)
expect(rows[0]).to_equal(0)
expect(rows[1]).to_equal(1)
expect(rows[2]).to_equal(2)
expect(stats.candidates_kept).to_equal(3)
expect(stats.rows_scanned).to_equal(4)
```

</details>

#### preserves matches across 31/32 and 63/64 bitmap boundaries

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = build_boundary_scan_values()
val predicate = ScanPredicate(kind: ScanPredicateKind.Contains, text_value: "src/", key_value: 0)
val (bitmap, stats) = scan_text_values(values, predicate)
expect(bitmap.get(0)).to_equal(true)
expect(bitmap.get(31)).to_equal(true)
expect(bitmap.get(32)).to_equal(true)
expect(bitmap.get(63)).to_equal(true)
expect(bitmap.get(64)).to_equal(true)
expect(bitmap.get(69)).to_equal(true)
expect(bitmap.count()).to_equal(6)
expect(stats.candidates_kept).to_equal(6)
```

</details>

### DB accel — capability report

#### reports runtime tier and keeps scalar fallback available

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = accel_capability_report()
expect(report.scalar_fallback).to_equal(true)
expect(report.tier_name.len()).to_be_greater_than(0)
expect(report.simd_width_bits).to_be_greater_than(-1)
expect(report.simd_active).to_equal(false)
```

</details>

#### uses deterministic summary hashes for scan prefilters

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(summary_text_hash("ab")).to_equal(summary_text_hash("ba"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/db/accel_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DB accel — bitmap operations
- DB accel — text predicates
- DB accel — batched scalar scans
- DB accel — capability report

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
