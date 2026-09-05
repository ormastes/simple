# MCP Log Store

> Tests the MCP log storage backend including log persistence, rotation, and retrieval. Verifies that log entries are correctly indexed, queryable by timestamp and severity, and that storage limits are enforced properly.

<!-- sdn-diagram:id=mcp_log_store_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_log_store_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_log_store_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_log_store_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Log Store

Tests the MCP log storage backend including log persistence, rotation, and retrieval. Verifies that log entries are correctly indexed, queryable by timestamp and severity, and that storage limits are enforced properly.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | In Progress |
| Source | `test/03_system/feature/app/mcp_log_store_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the MCP log storage backend including log persistence, rotation, and
retrieval. Verifies that log entries are correctly indexed, queryable by
timestamp and severity, and that storage limits are enforced properly.

## Scenarios

### MCP Log Store

#### keeps debug log JSON serialization available

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = log_store_source()

expect(source).to_contain("fn log_entry_to_json(entry: DebugLogEntry) -> text")
expect(source).to_contain("fn log_entries_to_json(entries: [DebugLogEntry]) -> text")
expect(source).to_contain("entry_id")
expect(source).to_contain("function_name")
expect(source).to_contain("duration_ms")
expect(source).to_contain("params_text")
```

</details>

#### keeps debug log tree JSON and folding metadata available

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = log_store_source()

expect(source).to_contain("fn log_tree_to_json(entries: [DebugLogEntry]) -> text")
expect(source).to_contain("fn log_tree_to_json_mode(entries: [DebugLogEntry], mode: text) -> text")
expect(source).to_contain("fn _build_tree_node_json")
expect(source).to_contain("fold_state")
expect(source).to_contain("default_open")
expect(source).to_contain("child_count")
```

</details>

#### keeps debug log text tree rendering available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = log_store_source()

expect(source).to_contain("fn format_log_tree_text(entries: [DebugLogEntry], expanded_groups: [i64]) -> text")
expect(source).to_contain("fn format_log_tree_text_mode(entries: [DebugLogEntry], expanded_groups: [i64], mode: text) -> text")
expect(source).to_contain("fn _entry_default_open(entry: DebugLogEntry) -> bool")
expect(source).to_contain("error")
expect(source).to_contain("fail")
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
