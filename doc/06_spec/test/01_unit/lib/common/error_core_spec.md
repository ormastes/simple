# Error Core Specification

> <details>

<!-- sdn-diagram:id=error_core_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=error_core_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

error_core_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=error_core_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Error Core Specification

## Scenarios

### ErrorCore

#### keeps canonical runtime error tagged value helper available

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = common_error_source()

expect(source).to_contain("pub fn rt_error_value() -> i64")
expect(source).to_contain("Return the canonical RT_ERROR tagged value")
expect(source).to_contain("27")
```

</details>

#### keeps method-not-found reporting aligned with RT_ERROR semantics

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = common_error_source()

expect(source).to_contain("pub fn rt_method_not_found(type_name: text, method_name: text) -> i64")
expect(source).to_contain("Runtime error: Method '{method_name}' not found on type '{type_name}'")
expect(source).to_contain("returns RT_ERROR")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/error_core_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ErrorCore

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
