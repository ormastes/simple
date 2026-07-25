# Tool Table Generators Specification

> <details>

<!-- sdn-diagram:id=tool_table_generators_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tool_table_generators_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tool_table_generators_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tool_table_generators_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tool Table Generators Specification

## Scenarios

### simple_feature_gen tool entry

#### has no name parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = _find_tool_entry("simple_feature_gen")
val has_name = entry.props.contains_key("name")
expect(has_name).to_equal(false)
```

</details>

#### has a non-empty description

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = _find_tool_entry("simple_feature_gen")
expect(entry.description.len() > 0).to_equal(true)
```

</details>

#### description mentions feature or regenerate

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = _find_tool_entry("simple_feature_gen")
val desc_lower = entry.description.lower()
val mentions_feature = desc_lower.contains("feature") or desc_lower.contains("regenerate")
expect(mentions_feature).to_equal(true)
```

</details>

### simple_task_gen tool entry

#### has no name parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = _find_tool_entry("simple_task_gen")
val has_name = entry.props.contains_key("name")
expect(has_name).to_equal(false)
```

</details>

#### has a non-empty description

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = _find_tool_entry("simple_task_gen")
expect(entry.description.len() > 0).to_equal(true)
```

</details>

### simple_todo_gen tool entry

#### has read_only set to true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = _find_tool_entry("simple_todo_gen")
expect(entry.read_only).to_equal(true)
```

</details>

### simple_spec_gen tool entry

#### has path parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = _find_tool_entry("simple_spec_gen")
val has_path = entry.props.contains_key("path")
expect(has_path).to_equal(true)
```

</details>

### simple_spec_coverage tool entry

#### has read_only set to true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = _find_tool_entry("simple_spec_coverage")
expect(entry.read_only).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp/tool_table_generators_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- simple_feature_gen tool entry
- simple_task_gen tool entry
- simple_todo_gen tool entry
- simple_spec_gen tool entry
- simple_spec_coverage tool entry

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
