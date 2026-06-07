# Export As Runtime Bug Specification

> <details>

<!-- sdn-diagram:id=export_as_runtime_bug_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=export_as_runtime_bug_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

export_as_runtime_bug_spec -> bugs
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=export_as_runtime_bug_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Export As Runtime Bug Specification

## Scenarios

### Export As Runtime Bug

#### demonstrates working workaround using wrapper functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result1 = aliased_function(5)
val result2 = renamed_function(5)

expect(result1).to_equal(10)
expect(result2).to_equal(15)
```

</details>

#### documents the broken export alias syntax in the fixture

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = export_as_module_source()

expect(source).to_contain("# export original_function as aliased_function")
expect(source).to_contain("# export another_function as renamed_function")
```

</details>

#### documents the active wrapper export used until alias syntax works

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = export_as_module_source()

expect(source).to_contain("fn aliased_function(x: i64) -> i64")
expect(source).to_contain("fn renamed_function(x: i64) -> i64")
expect(source).to_contain("export aliased_function, renamed_function")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Bug Regression |
| Status | Active |
| Source | `test/01_unit/bugs/export_as_runtime_bug_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Export As Runtime Bug

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
