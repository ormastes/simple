# Db Accel Facade Specification

> 1. bitmap set

<!-- sdn-diagram:id=db_accel_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=db_accel_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

db_accel_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=db_accel_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Db Accel Facade Specification

## Scenarios

### gc_async_mut DB acceleration facade

#### re-exports bitmap operations from the canonical DB accel module

1. bitmap set
2. bitmap set
   - Expected: bitmap.count() equals `2`
   - Expected: bitmap.get(39) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bitmap = RowBitmap.empty(40)
bitmap.set(0)
bitmap.set(39)

expect(bitmap.count()).to_equal(2)
expect(bitmap.get(39)).to_equal(true)
```

</details>

#### re-exports scan helpers and text predicates

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val predicate = ScanPredicate(kind: ScanPredicateKind.Eq, text_value: "", key_value: 7)
val (bitmap, stats) = scan_key_span(make_key_span([7, 8, 7], 0, 3), predicate)

expect(bitmap.count()).to_equal(2)
expect(stats.rows_scanned).to_equal(3)
expect(text_contains_token("alpha|beta", "beta")).to_equal(true)
expect(trigram_overlap_count("token", "stokenized")).to_be_greater_than(0)
```

</details>

#### reports scalar fallback availability

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = accel_capability_report()
expect(report.scalar_fallback).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/db/db_accel_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut DB acceleration facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
