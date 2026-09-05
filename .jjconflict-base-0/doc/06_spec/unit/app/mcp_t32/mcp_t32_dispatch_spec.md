# Mcp T32 Dispatch Specification

> Tests covering T32 MCP Tool Dispatch.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp T32 Dispatch Specification

## Scenarios

### T32 MCP Tool Dispatch

#### routes session tools (4 tools)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- routes session tools (4 tools)
   - Expected: mock_dispatch("t32_sessions_list") equals `sessions_list`
   - Expected: mock_dispatch("t32_session_open") equals `session_open`
   - Expected: mock_dispatch("t32_session_resume") equals `session_resume`
   - Expected: mock_dispatch("t32_session_close") equals `session_close`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes session tools (4 tools)")
expect(mock_dispatch("t32_sessions_list")).to_equal("sessions_list")
expect(mock_dispatch("t32_session_open")).to_equal("session_open")
expect(mock_dispatch("t32_session_resume")).to_equal("session_resume")
expect(mock_dispatch("t32_session_close")).to_equal("session_close")
```

</details>

#### routes core tools (2 tools)

- routes core tools (2 tools)
   - Expected: mock_dispatch("t32_core_list") equals `core_list`
   - Expected: mock_dispatch("t32_core_select") equals `core_select`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes core tools (2 tools)")
expect(mock_dispatch("t32_core_list")).to_equal("core_list")
expect(mock_dispatch("t32_core_select")).to_equal("core_select")
```

</details>

#### routes command tools (3 tools)

- routes command tools (3 tools)
   - Expected: mock_dispatch("t32_cmd_run") equals `cmd_run`
   - Expected: mock_dispatch("t32_cmm_run") equals `cmm_run`
   - Expected: mock_dispatch("t32_eval") equals `eval`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes command tools (3 tools)")
expect(mock_dispatch("t32_cmd_run")).to_equal("cmd_run")
expect(mock_dispatch("t32_cmm_run")).to_equal("cmm_run")
expect(mock_dispatch("t32_eval")).to_equal("eval")
```

</details>

#### routes window tools (4 tools)

- routes window tools (4 tools)
   - Expected: mock_dispatch("t32_window_list") equals `window_list`
   - Expected: mock_dispatch("t32_window_open") equals `window_open`
   - Expected: mock_dispatch("t32_window_capture") equals `window_capture`
   - Expected: mock_dispatch("t32_window_describe") equals `window_describe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes window tools (4 tools)")
expect(mock_dispatch("t32_window_list")).to_equal("window_list")
expect(mock_dispatch("t32_window_open")).to_equal("window_open")
expect(mock_dispatch("t32_window_capture")).to_equal("window_capture")
expect(mock_dispatch("t32_window_describe")).to_equal("window_describe")
```

</details>

#### routes screenshot tool

- routes screenshot tool
   - Expected: mock_dispatch("t32_screenshot") equals `screenshot`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes screenshot tool")
expect(mock_dispatch("t32_screenshot")).to_equal("screenshot")
```

</details>

#### routes action/field tools (3 tools)

- routes action/field tools (3 tools)
   - Expected: mock_dispatch("t32_action_invoke") equals `action_invoke`
   - Expected: mock_dispatch("t32_field_get") equals `field_get`
   - Expected: mock_dispatch("t32_field_set") equals `field_set`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes action/field tools (3 tools)")
expect(mock_dispatch("t32_action_invoke")).to_equal("action_invoke")
expect(mock_dispatch("t32_field_get")).to_equal("field_get")
expect(mock_dispatch("t32_field_set")).to_equal("field_set")
```

</details>

#### routes history tool

- routes history tool
   - Expected: mock_dispatch("t32_history_tail") equals `history_tail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes history tool")
expect(mock_dispatch("t32_history_tail")).to_equal("history_tail")
```

</details>

#### routes resource tools (2 tools)

- routes resource tools (2 tools)
   - Expected: mock_dispatch("t32_resources_list") equals `resources_list`
   - Expected: mock_dispatch("t32_resource_read") equals `resource_read`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes resource tools (2 tools)")
expect(mock_dispatch("t32_resources_list")).to_equal("resources_list")
expect(mock_dispatch("t32_resource_read")).to_equal("resource_read")
```

</details>

#### routes headless tools (3 tools)

- routes headless tools (3 tools)
   - Expected: mock_dispatch("t32_setup_headless") equals `setup_headless`
   - Expected: mock_dispatch("t32_area_read") equals `area_read`
   - Expected: mock_dispatch("t32_cmm_commands") equals `cmm_commands`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes headless tools (3 tools)")
expect(mock_dispatch("t32_setup_headless")).to_equal("setup_headless")
expect(mock_dispatch("t32_area_read")).to_equal("area_read")
expect(mock_dispatch("t32_cmm_commands")).to_equal("cmm_commands")
```

</details>

#### handles unknown tool

- handles unknown tool
   - Expected: mock_dispatch("nonexistent") equals `unknown`
   - Expected: mock_dispatch("") equals `unknown`
   - Expected: mock_dispatch("t32_bogus") equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles unknown tool")
expect(mock_dispatch("nonexistent")).to_equal("unknown")
expect(mock_dispatch("")).to_equal("unknown")
expect(mock_dispatch("t32_bogus")).to_equal("unknown")
```

</details>

#### covers all 23 tools

- covers all 23 tools
   - Expected: all_tools.len() equals `23`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers all 23 tools")
val all_tools = [
    "t32_sessions_list", "t32_session_open", "t32_session_resume", "t32_session_close",
    "t32_core_list", "t32_core_select",
    "t32_cmd_run", "t32_cmm_run", "t32_eval",
    "t32_window_list", "t32_window_open", "t32_window_capture", "t32_window_describe",
    "t32_screenshot",
    "t32_action_invoke", "t32_field_get", "t32_field_set",
    "t32_history_tail",
    "t32_resources_list", "t32_resource_read",
    "t32_setup_headless", "t32_area_read", "t32_cmm_commands"
]
expect(all_tools.len()).to_equal(23)
for tool in all_tools:
    val result = mock_dispatch(tool)
    expect(result).to_not_equal("unknown")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_t32/mcp_t32_dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32 MCP Tool Dispatch.
- T32 MCP Tool Dispatch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `3efb5020014fec079630307cdef3ca9951f4d2e012665f0fb88835766551d9a9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3efb5020014fec079630307cdef3ca9951f4d2e012665f0fb88835766551d9a9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3efb5020014fec079630307cdef3ca9951f4d2e012665f0fb88835766551d9a9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/app/mcp_t32/mcp_t32_dispatch_spec.spl
mirror: doc/06_spec/unit/app/mcp_t32/mcp_t32_dispatch_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_t32/mcp_t32_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_t32/mcp_t32_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_t32/mcp_t32_dispatch_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/mcp_t32/mcp_t32_dispatch_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes session tools (4 tools)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_t32/mcp_t32_dispatch_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes core tools (2 tools)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_t32/mcp_t32_dispatch_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes command tools (3 tools)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
