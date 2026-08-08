# Error Specification

> <details>

<!-- sdn-diagram:id=error_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=error_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

error_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=error_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Error Specification

## Scenarios

### Error

#### keeps pure Simple runtime error helpers independent of unknown externs

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = common_error_source()

expect(source).to_contain("Runtime error helpers")
expect(source).to_contain("pure Simple equivalents")
expect(source).to_contain("pub fn rt_error_value() -> i64")
expect(source).to_contain("pub fn rt_method_not_found(type_name: text, method_name: text) -> i64")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/error_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Error

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
