# Text Formatter Specification

> <details>

<!-- sdn-diagram:id=text_formatter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=text_formatter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

text_formatter_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=text_formatter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Text Formatter Specification

## Scenarios

### Text Formatter

#### keeps terminal formatting helpers available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = llm_text_formatter_source()

expect(source).to_contain("fn pad_right(s: text, width: i64) -> text")
expect(source).to_contain("fn pad_left(s: text, width: i64) -> text")
expect(source).to_contain("fn sep_line(width: i64) -> text")
expect(source).to_contain("fn format_tokens_k(n: i64) -> text")
```

</details>

#### keeps diagnostics section formatters available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = llm_text_formatter_source()

expect(source).to_contain("fn format_token_usage_text(u: TokenUsage) -> text")
expect(source).to_contain("fn format_mcp_stats_text(stats: [McpServerStats]) -> text")
expect(source).to_contain("fn format_agent_tree_text(agents: [AgentNode]) -> text")
expect(source).to_contain("fn format_timeline_text(events: [DiagEvent]) -> text")
expect(source).to_contain("fn format_cache_text(ca: CacheAnalysis) -> text")
```

</details>

#### keeps full session text report structure available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = llm_text_formatter_source()

expect(source).to_contain("fn format_session_text(session: SessionDiag) -> text")
expect(source).to_contain("=== LLM Diagnostics ===")
expect(source).to_contain("--- Token Usage ---")
expect(source).to_contain("--- MCP Servers ---")
expect(source).to_contain("--- Subagents ---")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/diagnostics/text_formatter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Text Formatter

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
