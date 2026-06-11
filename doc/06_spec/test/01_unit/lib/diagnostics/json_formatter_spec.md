# Json Formatter Specification

> <details>

<!-- sdn-diagram:id=json_formatter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=json_formatter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

json_formatter_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=json_formatter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Json Formatter Specification

## Scenarios

### Json Formatter

#### keeps JSON primitive formatter helpers available

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = json_formatter_source()

expect(source).to_contain("fn jp(key: text, value: text) -> text")
expect(source).to_contain("fn js(value: text) -> text")
expect(source).to_contain("fn jn(value: i64) -> text")
expect(source).to_contain("fn jb(value: bool) -> text")
expect(source).to_contain("fn ja(items: [text]) -> text")
expect(source).to_contain("fn escape_json_simple(s: text) -> text")
```

</details>

#### keeps JSON session diagnostic sections available

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = json_formatter_source()

expect(source).to_contain("fn format_token_usage_json(u: TokenUsage) -> text")
expect(source).to_contain("fn format_event_json(e: DiagEvent) -> text")
expect(source).to_contain("fn format_tool_call_json(tc: ToolCall) -> text")
expect(source).to_contain("fn format_mcp_stats_json(stats: [McpServerStats]) -> text")
expect(source).to_contain("fn format_agent_tree_json(agents: [AgentNode]) -> text")
expect(source).to_contain("fn format_session_json(session: SessionDiag) -> text")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/diagnostics/json_formatter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Json Formatter

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
