# Mcp Session Tools Specification

> Tests covering editor MCP session tools.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Session Tools Specification

## Scenarios

### editor MCP session tools

#### supports only the safe live MCP subset

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- supports only the safe live MCP subset
   - Expected: editor_mcp_session_tool_supported("editor.open_file") is true
   - Expected: editor_mcp_session_tool_supported("editor.read_buffer") is true
   - Expected: editor_mcp_session_tool_supported("editor.list_open_files") is true
   - Expected: editor_mcp_session_tool_supported("editor.edit") is false
   - Expected: editor_mcp_session_tool_supported("editor.search") is false
   - Expected: editor_mcp_session_tool_supported("editor.diagnostics") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports only the safe live MCP subset")
expect(editor_mcp_session_tool_supported("editor.open_file")).to_equal(true)
expect(editor_mcp_session_tool_supported("editor.read_buffer")).to_equal(true)
expect(editor_mcp_session_tool_supported("editor.list_open_files")).to_equal(true)
expect(editor_mcp_session_tool_supported("editor.edit")).to_equal(false)
expect(editor_mcp_session_tool_supported("editor.search")).to_equal(false)
expect(editor_mcp_session_tool_supported("editor.diagnostics")).to_equal(false)
```

</details>

#### opens files through the stateful bridge

- opens files through the stateful bridge
   - Expected: rt_file_write_text(path, "# Note\n\nhello from shared editor session\n") is true
   - Expected: opened.ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("opens files through the stateful bridge")
val path = "/tmp/simple_editor_mcp_session_tools_note.md"
expect(rt_file_write_text(path, "# Note\n\nhello from shared editor session\n")).to_equal(true)

var bridge = EditorMcpSessionBridge(session: EditSession.new())
val opened = bridge.dispatch("editor.open_file", [path])
expect(opened.ok).to_equal(true)
expect(opened.content).to_contain(path)
```

</details>

#### reads the active buffer through the stateful bridge

- reads the active buffer through the stateful bridge
   - Expected: rt_file_write_text(path, "# Note\n\nhello from shared editor session\n") is true
   - Expected: opened.ok is true
   - Expected: read.ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads the active buffer through the stateful bridge")
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

- lists open files through the stateful bridge
   - Expected: rt_file_write_text(path, "# Note\n\nhello from shared editor session\n") is true
   - Expected: opened.ok is true
   - Expected: listed.ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists open files through the stateful bridge")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering editor MCP session tools.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `05fef7ef87c952c146d8e2db380f8f02e5c056a091fc3413dc5565415300d3b5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `05fef7ef87c952c146d8e2db380f8f02e5c056a091fc3413dc5565415300d3b5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `05fef7ef87c952c146d8e2db380f8f02e5c056a091fc3413dc5565415300d3b5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/editor/mcp_session_tools_spec.spl
mirror: doc/06_spec/01_unit/lib/editor/mcp_session_tools_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/editor/mcp_session_tools_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/editor/mcp_session_tools_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/editor/mcp_session_tools_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports only the safe live MCP subset' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/editor/mcp_session_tools_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'opens files through the stateful bridge' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/editor/mcp_session_tools_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads the active buffer through the stateful bridge' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
