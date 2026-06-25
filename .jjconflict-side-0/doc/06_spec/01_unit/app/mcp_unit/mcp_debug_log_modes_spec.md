# Mcp Debug Log Modes Specification

> 1.  entry

<!-- sdn-diagram:id=mcp_debug_log_modes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_debug_log_modes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_debug_log_modes_spec -> std
mcp_debug_log_modes_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_debug_log_modes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Debug Log Modes Specification

## Scenarios

### MCP debug log modes

#### emits fold metadata in JSON tree mode

1.  entry
2.  entry
3.  entry
4.  entry


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entries = [
    _entry(1, 10, 0, 0, "enter", "root", 0, ""),
    _entry(2, 11, 10, 1, "enter", "child", 0, ""),
    _entry(3, 11, 10, 1, "exit", "child", 7, ""),
    _entry(4, 10, 0, 0, "exit", "root", 9, ""),
]
val json = log_tree_to_json_mode(entries, "human")
expect(json).to_contain("\"mode\":\"human\"")
expect(json).to_contain("\"has_children\":true")
expect(json).to_contain("\"child_count\":1")
expect(json).to_contain("\"collapsed_count\":1")
expect(json).to_contain("\"fold_state\":\"collapsed\"")
expect(json).to_contain("\"package_path_delta\":\"\"")
expect(json).to_contain("\"repeated_package\":true")
```

</details>

#### opens error groups by default in JSON tree mode

1.  entry


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entries = [
    _entry(1, 20, 0, 0, "enter", "load_error", 0, "error: failed"),
]
val json = log_tree_to_json_mode(entries, "human")
expect(json).to_contain("\"fold_state\":\"open\"")
expect(json).to_contain("\"default_open\":true")
```

</details>

#### renders compact LLM text mode

1.  entry
2.  entry
3.  entry
   - Expected: text does not contain `<<`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entries = [
    _entry(1, 30, 0, 0, "enter", "root", 0, ""),
    _entry(2, 31, 30, 1, "enter", "child", 0, ""),
    _entry(3, 31, 30, 1, "exit", "child", 3, ""),
]
val text = format_log_tree_text_mode(entries, [], "llm")
expect(text).to_contain("log_tree mode=llm entries=3")
expect(text).to_contain("- gid=30 depth=0 fn=app.test::root")
expect(text).to_contain("- gid=31 depth=1 fn=app.test::child")
expect(text.contains("<<")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/mcp_debug_log_modes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MCP debug log modes

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
