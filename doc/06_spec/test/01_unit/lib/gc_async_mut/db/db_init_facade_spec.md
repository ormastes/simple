# Db Init Facade Specification

> <details>

<!-- sdn-diagram:id=db_init_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=db_init_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

db_init_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=db_init_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Db Init Facade Specification

## Scenarios

### gc_async_mut DB package facade

#### re-exports acceleration and DBFS driver surfaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val predicate = ScanPredicate(kind: ScanPredicateKind.Gt, text_value: "", key_value: 2)
val (bitmap, _stats) = scan_key_span(make_key_span([1, 3, 4], 0, 3), predicate)
val empty = RowBitmap.empty(1)
val driver = DbFsDriver.new_hosted()

expect(bitmap.count()).to_equal(2)
expect(empty.count()).to_equal(0)
expect(driver.preferred_batch_bytes()).to_equal(4096)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/db/db_init_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut DB package facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
