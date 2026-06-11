# Native Enum U8 Regression Specification

> 1. enc push

<!-- sdn-diagram:id=native_enum_u8_regression_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_enum_u8_regression_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_enum_u8_regression_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_enum_u8_regression_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Enum U8 Regression Specification

## Scenarios

### native u8 regression

#### compares direct u8 index with u8 literal

1. enc push
   - Expected: enc[0].to_i64() equals `23`
   - Expected: enc[0] == 0x17u8 is true
   - Expected: enc[0] != 0x17u8 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var enc: [u8] = []
enc.push(0x17u8)

expect(enc[0].to_i64()).to_equal(23)
expect(enc[0] == 0x17u8).to_equal(true)
expect(enc[0] != 0x17u8).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/native_enum_u8_regression_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- native u8 regression

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
