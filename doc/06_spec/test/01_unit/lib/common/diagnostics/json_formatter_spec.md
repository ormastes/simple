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
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Json Formatter Specification

## Scenarios

### Json Formatter

#### keeps JSON primitive builders and escaping available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = llm_json_formatter_source()

expect(source).to_contain("fn jp(key: text, value: text) -> text")
expect(source).to_contain("fn js(value: text) -> text")
expect(source).to_contain("fn ja(items: [text]) -> text")
expect(source).to_contain("fn jo(pairs: [text]) -> text")
expect(source).to_contain("fn escape_json_simple(s: text) -> text")
```

</details>

#### keeps diagnostics JSON object formatters available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = llm_json_formatter_source()

expect(source).to_contain("fn format_token_usage_json(u: TokenUsage) -> text")
expect(source).to_contain("fn format_event_json(e: DiagEvent) -> text")
expect(source).to_contain("fn format_tool_call_json(tc: ToolCall) -> text")
expect(source).to_contain("fn format_mcp_stats_json(stats: [McpServerStats]) -> text")
expect(source).to_contain("fn format_agent_tree_json(agents: [AgentNode]) -> text")
```

</details>

#### keeps full session JSON report structure available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = llm_json_formatter_source()

expect(source).to_contain("fn format_session_json(session: SessionDiag) -> text")
expect(source).to_contain("jp(\"session_id\", js(session.session_id))")
expect(source).to_contain("jp(\"usage\", format_token_usage_json(session.total_usage))")
expect(source).to_contain("jp(\"mcp_stats\", format_mcp_stats_json(session.mcp_stats))")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/diagnostics/json_formatter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Json Formatter

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
