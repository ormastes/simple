# Simple Db If Facade Specification

> <details>

<!-- sdn-diagram:id=simple_db_if_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_db_if_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_db_if_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_db_if_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Db If Facade Specification

## Scenarios

### nogc_async_mut simple_db_if facade

#### re-exports DB interface value types

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Rel.null().is_null()).to_equal(true)
expect(BlkNo.first().n).to_equal(0)
expect(Lsn.zero().precedes(Lsn(value: 10))).to_equal(true)
expect(TxnId.null().id).to_equal(0)
expect(PhysPtr.null().is_null()).to_equal(true)

val page = PageBuf(arena_id: 1, offset: 2, length: 4096, generation: 3)
expect(page.length).to_equal(4096)
expect(page.generation).to_equal(3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/simple_db_if/simple_db_if_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut simple_db_if facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
