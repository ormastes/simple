# MCP Debug Log Tools

> Tests the MCP debug logging tools including log capture, filtering, and query capabilities. Verifies that debug logs are correctly stored, searchable, and can be streamed or exported for diagnostic analysis.

<!-- sdn-diagram:id=mcp_debug_log_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_debug_log_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_debug_log_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_debug_log_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Debug Log Tools

Tests the MCP debug logging tools including log capture, filtering, and query capabilities. Verifies that debug logs are correctly stored, searchable, and can be streamed or exported for diagnostic analysis.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | In Progress |
| Source | `test/03_system/feature/app/mcp_debug_log_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the MCP debug logging tools including log capture, filtering, and query
capabilities. Verifies that debug logs are correctly stored, searchable, and
can be streamed or exported for diagnostic analysis.

## Scenarios

### MCP Debug Log Tools

#### keeps debug log tool schemas available

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = debug_log_source()

expect(source).to_contain("fn schema_debug_log_enable() -> text")
expect(source).to_contain("fn schema_debug_log_disable() -> text")
expect(source).to_contain("fn schema_debug_log_clear() -> text")
expect(source).to_contain("fn schema_debug_log_query() -> text")
expect(source).to_contain("fn schema_debug_log_tree() -> text")
expect(source).to_contain("fn schema_debug_log_status() -> text")
expect(source).to_contain("readOnlyHint")
expect(source).to_contain("destructiveHint")
```

</details>

#### keeps debug log tool handlers available

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = debug_log_source()

expect(source).to_contain("fn handle_debug_log_enable(id: text, body: text) -> text")
expect(source).to_contain("fn handle_debug_log_disable(id: text) -> text")
expect(source).to_contain("fn handle_debug_log_clear(id: text) -> text")
expect(source).to_contain("fn handle_debug_log_query(id: text, body: text) -> text")
expect(source).to_contain("fn handle_debug_log_tree(id: text, body: text) -> text")
expect(source).to_contain("fn handle_debug_log_status(id: text) -> text")
expect(source).to_contain("debug_log_get_entries_since")
```

</details>

#### keeps debug log resource endpoint available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = debug_log_source()

expect(source).to_contain("fn handle_debuglog_resource")
expect(source).to_contain("debuglog://")
expect(source).to_contain("/status")
expect(source).to_contain("/entries")
expect(source).to_contain("/tree")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
