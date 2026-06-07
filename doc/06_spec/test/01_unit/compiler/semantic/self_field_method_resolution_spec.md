# Self Field Method Resolution Specification

> <details>

<!-- sdn-diagram:id=self_field_method_resolution_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=self_field_method_resolution_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

self_field_method_resolution_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=self_field_method_resolution_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Self Field Method Resolution Specification

## Scenarios

### self.field.method() resolution

#### dispatches through struct field to correct method

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val outer_val = make_outer(42)
val result = outer_val.trigger()
expect(result).to_equal(42)
```

</details>

#### two-level chained field method call returns correct value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val outer_val = make_outer(7)
val result = outer_val.trigger()
expect(result).to_equal(7)
```

</details>

#### field method result used in arithmetic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val outer_val = make_outer(10)
val doubled = outer_val.trigger() * 2
expect(doubled).to_equal(20)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantic/self_field_method_resolution_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- self.field.method() resolution

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
