# Posting List Bitmap Specification

> <details>

<!-- sdn-diagram:id=posting_list_bitmap_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=posting_list_bitmap_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

posting_list_bitmap_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=posting_list_bitmap_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Posting List Bitmap Specification

## Scenarios

### DB posting-list bitmap primitives

#### materializes one posting list into a row bitmap

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = posting_list_to_bitmap(posting_list_new("simple", [1, 3, 5]), 8)
val rows = posting_bitmap_result_rows(result)

expect(result.terms_evaluated).to_equal(1)
expect(result.postings_scanned).to_equal(3)
expect(result.rows_matched).to_equal(3)
expect(rows).to_equal([1, 3, 5])
```

</details>

#### evaluates token AND with bitmap intersection

1. posting list new
2. posting list new
3. posting list new
   - Expected: result.terms_evaluated equals `3`
   - Expected: result.postings_scanned equals `10`
   - Expected: result.rows_matched equals `1`
   - Expected: rows equals `[4]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = posting_lists_and_bitmap([
    posting_list_new("simple", [1, 2, 4, 8]),
    posting_list_new("database", [2, 4, 6]),
    posting_list_new("index", [4, 7, 8])
], 10)
val rows = posting_bitmap_result_rows(result)

expect(result.terms_evaluated).to_equal(3)
expect(result.postings_scanned).to_equal(10)
expect(result.rows_matched).to_equal(1)
expect(rows).to_equal([4])
```

</details>

#### evaluates token OR with bitmap union and deduplication

1. posting list new
2. posting list new
   - Expected: result.terms_evaluated equals `2`
   - Expected: result.postings_scanned equals `6`
   - Expected: result.rows_matched equals `5`
   - Expected: rows equals `[1, 2, 3, 4, 5]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = posting_lists_or_bitmap([
    posting_list_new("simple", [1, 2, 4]),
    posting_list_new("database", [2, 3, 5])
], 8)
val rows = posting_bitmap_result_rows(result)

expect(result.terms_evaluated).to_equal(2)
expect(result.postings_scanned).to_equal(6)
expect(result.rows_matched).to_equal(5)
expect(rows).to_equal([1, 2, 3, 4, 5])
```

</details>

#### returns empty rows for empty AND input

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = posting_lists_and_bitmap([], 12)
val rows = posting_bitmap_result_rows(result)

expect(result.terms_evaluated).to_equal(0)
expect(result.postings_scanned).to_equal(0)
expect(result.rows_matched).to_equal(0)
expect(rows.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/db/posting_list_bitmap_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DB posting-list bitmap primitives

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
