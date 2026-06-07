# Src Time Facade Specification

> <details>

<!-- sdn-diagram:id=src_time_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=src_time_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

src_time_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=src_time_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Src Time Facade Specification

## Scenarios

### nogc_async_mut src time facade

#### re-exports time read helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(now_micros() > 0).to_equal(true)
expect(now_nanos() > 0).to_equal(true)
expect(now_ms() > 0).to_equal(true)
expect(now() > 0.0).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/src/src_time_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut src time facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
