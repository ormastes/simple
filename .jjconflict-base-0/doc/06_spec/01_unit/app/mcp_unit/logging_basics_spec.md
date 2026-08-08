# Logging Basics Specification

> <details>

<!-- sdn-diagram:id=logging_basics_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=logging_basics_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

logging_basics_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=logging_basics_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Logging Basics Specification

## Scenarios

### Logging Basics

#### defines debug log JSON serialization helpers

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/lib/nogc_async_mut/mcp/log_store.spl")

expect(src).to_contain("fn _escape_json_local(value: text) -> text:")
expect(src).to_contain("fn _json_string(value: text) -> text:")
expect(src).to_contain("fn log_entry_to_json(entry: DebugLogEntry) -> text:")
expect(src).to_contain("entry_id")
expect(src).to_contain("function_name")
expect(src).to_contain("duration_ms")
expect(src).to_contain("fn log_entries_to_json(entries: [DebugLogEntry]) -> text:")
```

</details>

#### defines debug log tree rendering contracts

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/lib/nogc_async_mut/mcp/log_store.spl")

expect(src).to_contain("fn log_tree_to_json(entries: [DebugLogEntry]) -> text:")
expect(src).to_contain("fn log_tree_to_json_mode(entries: [DebugLogEntry], mode: text) -> text:")
expect(src).to_contain("children_by_parent")
expect(src).to_contain("duration_by_gid")
expect(src).to_contain("fn _build_tree_node_json")
expect(src).to_contain("fold_state")
expect(src).to_contain("fn _entry_default_open(entry: DebugLogEntry) -> bool:")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/logging_basics_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Logging Basics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
