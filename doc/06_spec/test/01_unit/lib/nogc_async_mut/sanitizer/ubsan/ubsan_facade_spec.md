# Ubsan Facade Specification

> 1. ubsan reset

<!-- sdn-diagram:id=ubsan_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ubsan_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ubsan_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ubsan_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ubsan Facade Specification

## Scenarios

### nogc_async_mut sanitizer ubsan facade

#### re-exports undefined-behavior sanitizer checks and records

1. ubsan reset
   - Expected: ubsan_is_enabled() is false
   - Expected: ubsan_check_not_nil(0, "disabled") is true
2. ubsan enable
   - Expected: ubsan_is_enabled() is true
   - Expected: ubsan_check_not_nil(0, "load") is false
   - Expected: ubsan_div_i64(10, 0) equals `0`
   - Expected: ubsan_check_index(2, 5) is false
   - Expected: ubsan_error_count() equals `3`
   - Expected: ubsan_get_events()[0].kind equals `ubsan`
   - Expected: violation.kind equals `overflow`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ubsan_reset()
expect(ubsan_is_enabled()).to_equal(false)
expect(ubsan_check_not_nil(0, "disabled")).to_equal(true)

ubsan_enable()
expect(ubsan_is_enabled()).to_equal(true)
expect(ubsan_check_not_nil(0, "load")).to_equal(false)
expect(ubsan_div_i64(10, 0)).to_equal(0)
expect(ubsan_check_index(2, 5)).to_equal(false)
expect(ubsan_error_count()).to_equal(3)
expect(ubsan_get_events()[0].kind).to_equal("ubsan")

val violation = ub_violation("overflow", "bad add", "test")
expect(violation.kind).to_equal("overflow")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/sanitizer/ubsan/ubsan_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut sanitizer ubsan facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
