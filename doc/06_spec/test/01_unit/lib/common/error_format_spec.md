# Error Format Specification

> <details>

<!-- sdn-diagram:id=error_format_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=error_format_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

error_format_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=error_format_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Error Format Specification

## Scenarios

### Error Format

#### keeps runtime error diagnostics human-readable

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = common_error_source()

expect(source).to_contain("Method '{method_name}' not found")
expect(source).to_contain("type '{type_name}'")
expect(source).to_contain("print(\"Runtime error:")
```

</details>

#### keeps duplicate-symbol avoidance documented for function-not-found

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = common_error_source()

expect(source).to_contain("does NOT redefine rt_function_not_found")
expect(source).to_contain("duplicate-symbol collision")
expect(source).to_contain("Only rt_method_not_found is added here")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/error_format_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Error Format

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
