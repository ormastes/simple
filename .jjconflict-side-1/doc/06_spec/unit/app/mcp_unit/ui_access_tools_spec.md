# MCP UI Access Tools Specification

> Validates the ui_access MCP tool family: ui_access_snapshot, ui_access_surface, ui_access_find, ui_access_act, ui_access_history, ui_access_observe, ui_access_state, ui_access_query, ui_access_ensure, ui_access_value, ui_access_adapter_snapshot, ui_access_visual_probe.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP UI Access Tools Specification

Validates the ui_access MCP tool family: ui_access_snapshot, ui_access_surface, ui_access_find, ui_access_act, ui_access_history, ui_access_observe, ui_access_state, ui_access_query, ui_access_ensure, ui_access_value, ui_access_adapter_snapshot, ui_access_visual_probe.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #3031-3035 |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/unit/app/mcp_unit/ui_access_tools_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the ui_access MCP tool family:
ui_access_snapshot, ui_access_surface, ui_access_find, ui_access_act,
ui_access_history, ui_access_observe, ui_access_state, ui_access_query,
ui_access_ensure, ui_access_value, ui_access_adapter_snapshot,
ui_access_visual_probe.

The spec checks the tool vocabulary, tool-list exposure, and tools/call routing
behaviour using a local JSON-RPC mock.

## Scenarios

### ui_access tool family

#### tool vocabulary

#### contains twelve ui_access tools

- contains twelve ui_access tools
   - Expected: tools.len() equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains twelve ui_access tools")
val tools = [
    "ui_access_snapshot",
    "ui_access_surface",
    "ui_access_find",
    "ui_access_act",
    "ui_access_history",
    "ui_access_observe",
    "ui_access_state",
    "ui_access_query",
    "ui_access_ensure",
    "ui_access_value",
    "ui_access_adapter_snapshot",
    "ui_access_visual_probe"
]
expect(tools.len()).to_equal(12)
```

</details>

#### all ui_access tools use the canonical prefix

- all ui_access tools use the canonical prefix
   - Expected: tool.starts_with("ui_access_") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all ui_access tools use the canonical prefix")
val tools = [
    "ui_access_snapshot",
    "ui_access_surface",
    "ui_access_find",
    "ui_access_act",
    "ui_access_history",
    "ui_access_observe",
    "ui_access_state",
    "ui_access_query",
    "ui_access_ensure",
    "ui_access_value",
    "ui_access_adapter_snapshot",
    "ui_access_visual_probe"
]
for tool in tools:
    expect(tool.starts_with("ui_access_")).to_equal(true)
```

</details>

#### tools/list

#### advertises all ui_access tool names

- advertises all ui_access tool names
   - Expected: resp contains `"ui_access_snapshot"`
   - Expected: resp contains `"ui_access_surface"`
   - Expected: resp contains `"ui_access_find"`
   - Expected: resp contains `"ui_access_act"`
   - Expected: resp contains `"ui_access_history"`
   - Expected: resp contains `"ui_access_observe"`
   - Expected: resp contains `"ui_access_state"`
   - Expected: resp contains `"ui_access_query"`
   - Expected: resp contains `"ui_access_ensure"`
   - Expected: resp contains `"ui_access_value"`
   - Expected: resp contains `"ui_access_adapter_snapshot"`
   - Expected: resp contains `"ui_access_visual_probe"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("advertises all ui_access tool names")
val resp = handle_jsonrpc(make_req("1", "tools/list"))
expect(resp.contains("\"ui_access_snapshot\"")).to_equal(true)
expect(resp.contains("\"ui_access_surface\"")).to_equal(true)
expect(resp.contains("\"ui_access_find\"")).to_equal(true)
expect(resp.contains("\"ui_access_act\"")).to_equal(true)
expect(resp.contains("\"ui_access_history\"")).to_equal(true)
expect(resp.contains("\"ui_access_observe\"")).to_equal(true)
expect(resp.contains("\"ui_access_state\"")).to_equal(true)
expect(resp.contains("\"ui_access_query\"")).to_equal(true)
expect(resp.contains("\"ui_access_ensure\"")).to_equal(true)
expect(resp.contains("\"ui_access_value\"")).to_equal(true)
expect(resp.contains("\"ui_access_adapter_snapshot\"")).to_equal(true)
expect(resp.contains("\"ui_access_visual_probe\"")).to_equal(true)
```

</details>

#### tools/call

#### routes ui_access_snapshot

- routes ui_access_snapshot
   - Expected: resp contains `snapshot: ui_access_snapshot`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes ui_access_snapshot")
val resp = handle_jsonrpc(make_tool_call_req("2", "ui_access_snapshot", jo1("")))
expect(resp.contains("snapshot: ui_access_snapshot")).to_equal(true)
```

</details>

#### routes ui_access_surface

- routes ui_access_surface
   - Expected: resp contains `surface: main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes ui_access_surface")
val resp = handle_jsonrpc(make_tool_call_req("3", "ui_access_surface", jo1(jp("surface_id", js("main")))))
expect(resp.contains("surface: main")).to_equal(true)
```

</details>

#### routes ui_access_find

- routes ui_access_find
   - Expected: resp contains `find: button`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes ui_access_find")
val resp = handle_jsonrpc(make_tool_call_req("4", "ui_access_find", jo1(jp("kind", js("button")))))
expect(resp.contains("find: button")).to_equal(true)
```

</details>

#### routes ui_access_act

- routes ui_access_act
   - Expected: resp contains `act: click`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes ui_access_act")
val resp = handle_jsonrpc(make_tool_call_req("5", "ui_access_act", jo1(jp("action", js("click")))))
expect(resp.contains("act: click")).to_equal(true)
```

</details>

#### routes ui_access_history

- routes ui_access_history
   - Expected: resp contains `history: 5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes ui_access_history")
val resp = handle_jsonrpc(make_tool_call_req("6", "ui_access_history", jo1(jp("count", js("5")))))
expect(resp.contains("history: 5")).to_equal(true)
```

</details>

#### routes ui_access_observe

- routes ui_access_observe
   - Expected: resp contains `observe: main#submit_btn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes ui_access_observe")
val resp = handle_jsonrpc(make_tool_call_req("7", "ui_access_observe", jo1(jp("canonical_id", js("main#submit_btn")))))
expect(resp.contains("observe: main#submit_btn")).to_equal(true)
```

</details>

#### routes ui_access_state

- routes ui_access_state
   - Expected: resp contains `state: focused`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes ui_access_state")
val resp = handle_jsonrpc(make_tool_call_req("8", "ui_access_state", jo1(jp("state_key", js("focused")))))
expect(resp.contains("state: focused")).to_equal(true)
```

</details>

#### routes ui_access_query

- routes ui_access_query
   - Expected: resp contains `query: button`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes ui_access_query")
val resp = handle_jsonrpc(make_tool_call_req("9", "ui_access_query", jo1(jp("kind", js("button")))))
expect(resp.contains("query: button")).to_equal(true)
```

</details>

#### routes ui_access_ensure

- routes ui_access_ensure
   - Expected: resp contains `ensure: exists`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes ui_access_ensure")
val resp = handle_jsonrpc(make_tool_call_req("10", "ui_access_ensure", jo1(jp("expectation", js("exists")))))
expect(resp.contains("ensure: exists")).to_equal(true)
```

</details>

#### routes ui_access_value

- routes ui_access_value
   - Expected: resp contains `value: main#name_input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes ui_access_value")
val resp = handle_jsonrpc(make_tool_call_req("11", "ui_access_value", jo1(jp("canonical_id", js("main#name_input")))))
expect(resp.contains("value: main#name_input")).to_equal(true)
```

</details>

#### routes ui_access_adapter_snapshot

- routes ui_access_adapter_snapshot
   - Expected: resp contains `adapter_snapshot: main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes ui_access_adapter_snapshot")
val resp = handle_jsonrpc(make_tool_call_req("12", "ui_access_adapter_snapshot", jo1(jp("surface_id", js("main")))))
expect(resp.contains("adapter_snapshot: main")).to_equal(true)
```

</details>

#### routes ui_access_visual_probe

- routes ui_access_visual_probe
   - Expected: resp contains `visual_probe: main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes ui_access_visual_probe")
val resp = handle_jsonrpc(make_tool_call_req("13", "ui_access_visual_probe", jo1(jp("surface_id", js("main")))))
expect(resp.contains("visual_probe: main")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
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

- Canonical SPipe generation for source `689bc1e74a6937ca6b2d8b5b70fbe21a090b556b4b02cd87a6e5ec237ef420cf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `689bc1e74a6937ca6b2d8b5b70fbe21a090b556b4b02cd87a6e5ec237ef420cf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `689bc1e74a6937ca6b2d8b5b70fbe21a090b556b4b02cd87a6e5ec237ef420cf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/app/mcp_unit/ui_access_tools_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/ui_access_tools_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/ui_access_tools_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/ui_access_tools_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/ui_access_tools_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/mcp_unit/ui_access_tools_spec.spl:116:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'contains twelve ui_access tools' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/ui_access_tools_spec.spl:135:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'all ui_access tools use the canonical prefix' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/ui_access_tools_spec.spl:156:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'advertises all ui_access tool names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
