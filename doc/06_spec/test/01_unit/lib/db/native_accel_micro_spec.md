# Native Accel Micro Specification

> 1. bitmap clear

<!-- sdn-diagram:id=native_accel_micro_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_accel_micro_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_accel_micro_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_accel_micro_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Accel Micro Specification

## Scenarios

### native accel micro

#### mutates bitmap clear/get/count

1. bitmap clear
2. bitmap clear
3. bitmap clear
4. bitmap clear
   - Expected: bitmap.get(0) is false
   - Expected: bitmap.get(31) is false
   - Expected: bitmap.get(32) is false
   - Expected: bitmap.get(64) is false
   - Expected: bitmap.count() equals `61`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bitmap = RowBitmap.full(65)
expect(bitmap.count()).to_equal(65)
bitmap.clear(0)
bitmap.clear(31)
bitmap.clear(32)
bitmap.clear(64)
expect(bitmap.get(0)).to_equal(false)
expect(bitmap.get(31)).to_equal(false)
expect(bitmap.get(32)).to_equal(false)
expect(bitmap.get(64)).to_equal(false)
expect(bitmap.count()).to_equal(61)
```

</details>

#### evaluates text predicate helpers

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

#### evaluates delimiter helpers

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

#### reports simd capability coherently

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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/db/native_accel_micro_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- native accel micro

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
