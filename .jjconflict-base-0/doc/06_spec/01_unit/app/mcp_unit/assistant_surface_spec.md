# Assistant Surface Specification

> <details>

<!-- sdn-diagram:id=assistant_surface_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=assistant_surface_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

assistant_surface_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=assistant_surface_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Assistant Surface Specification

## Scenarios

### Assistant MCP Surface

#### publishes the core assistant tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = tool_names()
expect(has_tool(names, "assistant_start")).to_equal(true)
expect(has_tool(names, "assistant_spawn_task")).to_equal(true)
expect(has_tool(names, "assistant_pause")).to_equal(true)
expect(has_tool(names, "assistant_resume")).to_equal(true)
expect(has_tool(names, "assistant_brief")).to_equal(true)
expect(has_tool(names, "assistant_list_sessions")).to_equal(true)
expect(has_tool(names, "assistant_get_session")).to_equal(true)
expect(has_tool(names, "assistant_get_timeline")).to_equal(true)
expect(has_tool(names, "assistant_push_signal")).to_equal(true)
expect(has_tool(names, "assistant_list_tasks")).to_equal(true)
expect(has_tool(names, "assistant_get_notifications")).to_equal(true)
```

</details>

#### marks assistant tools as in-process handlers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
for entry in get_tool_table():
    if entry.name.starts_with("assistant_"):
        expect(entry.handler_kind).to_equal("in_process")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/assistant_surface_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Assistant MCP Surface

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
