# Native Combinators Specification

> <details>

<!-- sdn-diagram:id=native_combinators_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_combinators_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_combinators_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_combinators_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Combinators Specification

## Scenarios

### gc_sync_immut native combinators

#### runs pure combinators through the sync GC facade chain

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(pmap([2, 4], _1 + 5)).to_equal([7, 9])
expect(pfold([1, 2, 3, 4], 0, \acc, x: acc + x)).to_equal(10)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_sync_immut/native_combinators_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_sync_immut native combinators

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
