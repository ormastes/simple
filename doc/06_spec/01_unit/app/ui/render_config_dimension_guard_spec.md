# Render Config Dimension Guard Specification

> <details>

<!-- sdn-diagram:id=render_config_dimension_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=render_config_dimension_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

render_config_dimension_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=render_config_dimension_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Render Config Dimension Guard Specification

## Scenarios

### render config dimension guard

#### guards malformed environment dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/ui.render/config.spl") ?? ""

expect(source).to_contain("fn parse_env_dimension_or_default(value: text, default_value: i64) -> i64")
expect(source).to_contain("for ch in trimmed:")
expect(source).to_contain("if ch < \"0\" or ch > \"9\":")
expect(source).to_contain("val parsed = trimmed.to_int() ?? default_value")
expect(source).to_contain("result.width = parse_env_dimension_or_default(env_width, result.width)")
expect(source).to_contain("result.height = parse_env_dimension_or_default(env_height, result.height)")
expect(source.contains("result.width = env_width.to_int()")).to_equal(false)
expect(source.contains("result.height = env_height.to_int()")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/render_config_dimension_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- render config dimension guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
