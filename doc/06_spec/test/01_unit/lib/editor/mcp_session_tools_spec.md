# Mcp Session Tools Specification

> <details>

<!-- sdn-diagram:id=mcp_session_tools_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_session_tools_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_session_tools_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_session_tools_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Session Tools Specification

## Scenarios

### editor MCP session tools

#### supports only the safe live MCP subset

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(editor_mcp_session_tool_supported("editor.open_file")).to_equal(true)
expect(editor_mcp_session_tool_supported("editor.read_buffer")).to_equal(true)
expect(editor_mcp_session_tool_supported("editor.list_open_files")).to_equal(true)
expect(editor_mcp_session_tool_supported("editor.edit")).to_equal(false)
expect(editor_mcp_session_tool_supported("editor.search")).to_equal(false)
expect(editor_mcp_session_tool_supported("editor.diagnostics")).to_equal(false)
```

</details>

#### opens files through the stateful bridge

1. var bridge = EditorMcpSessionBridge
   - Expected: opened.ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/simple_editor_mcp_session_tools_note.md"
expect(rt_file_write_text(path, "# Note\n\nhello from shared editor session\n")).to_equal(true)

var bridge = EditorMcpSessionBridge(session: EditSession.new())
val opened = bridge.dispatch("editor.open_file", [path])
expect(opened.ok).to_equal(true)
expect(opened.content).to_contain(path)
```

</details>

#### reads the active buffer through the stateful bridge

1. var bridge = EditorMcpSessionBridge
   - Expected: opened.ok is true
   - Expected: read.ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/simple_editor_mcp_session_tools_note.md"
expect(rt_file_write_text(path, "# Note\n\nhello from shared editor session\n")).to_equal(true)
var bridge = EditorMcpSessionBridge(session: EditSession.new())
val opened = bridge.dispatch("editor.open_file", [path])
expect(opened.ok).to_equal(true)
val read = bridge.dispatch("editor.read_buffer", [])
expect(read.ok).to_equal(true)
expect(read.content).to_contain("hello from shared editor session")
```

</details>

#### lists open files through the stateful bridge

1. var bridge = EditorMcpSessionBridge
   - Expected: opened.ok is true
   - Expected: listed.ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/simple_editor_mcp_session_tools_note.md"
expect(rt_file_write_text(path, "# Note\n\nhello from shared editor session\n")).to_equal(true)
var bridge = EditorMcpSessionBridge(session: EditSession.new())
val opened = bridge.dispatch("editor.open_file", [path])
expect(opened.ok).to_equal(true)
val listed = bridge.dispatch("editor.list_open_files", [])
expect(listed.ok).to_equal(true)
expect(listed.content).to_contain(path)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/editor/mcp_session_tools_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- editor MCP session tools

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
