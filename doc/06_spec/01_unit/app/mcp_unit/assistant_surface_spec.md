# Assistant Surface Specification

> Tests covering Assistant MCP Surface.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Assistant Surface Specification

## Scenarios

### Assistant MCP Surface

#### publishes the core assistant tools

- publishes the core assistant tools


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("publishes the core assistant tools")
val names = tool_names()
expect(has_tool(names, "assistant_start")).to_be(true)
expect(has_tool(names, "assistant_spawn_task")).to_be(true)
expect(has_tool(names, "assistant_pause")).to_be(true)
expect(has_tool(names, "assistant_resume")).to_be(true)
expect(has_tool(names, "assistant_brief")).to_be(true)
expect(has_tool(names, "assistant_list_sessions")).to_be(true)
expect(has_tool(names, "assistant_get_session")).to_be(true)
expect(has_tool(names, "assistant_get_timeline")).to_be(true)
expect(has_tool(names, "assistant_push_signal")).to_be(true)
expect(has_tool(names, "assistant_list_tasks")).to_be(true)
expect(has_tool(names, "assistant_get_notifications")).to_be(true)
```

</details>

#### marks assistant tools as in-process handlers

- marks assistant tools as in-process handlers
   - Expected: entry.handler_kind equals `in_process`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("marks assistant tools as in-process handlers")
for entry in get_tool_table():
    if entry.name.starts_with("assistant_"):
        expect(entry.handler_kind).to_equal("in_process")
```

</details>

#### requires a path for duplicate-check tools

- requires a path for duplicate-check tools


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires a path for duplicate-check tools")
var found = false
for entry in get_tool_table():
    if entry.name == "simple_duplicate_check":
        found = true
        expect(entry.required_json).to_contain("\"path\"")
val static_tools = rt_file_read_text("src/app/mcp/main_static_tools.spl") ?? ""
expect(found).to_be(true)
expect(static_tools).to_contain("_mcp_static_tool(\"simple_duplicate_check\", \"[cli] Check for code duplication\", \"[\\\"path\\\"]\")")
```

</details>

#### requires signal timeline append success before state update

- requires signal timeline append success before state update


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires signal timeline append success before state update")
val source = rt_file_read_text("src/app/mcp/main_lazy_assistant.spl") ?? ""
expect(source).to_contain("val appended = assistant_store_append_event_record(ASSIST_ROOT, event_obj)")
expect(source).to_contain("if appended == nil:")
expect(source).to_contain("Failed to append signal event")
expect(source).to_contain("val updated = assistant_store_update_state")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/assistant_surface_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Assistant MCP Surface.
- Assistant MCP Surface

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

- Canonical SPipe generation for source `dac91c8d598306dc5bc0c1a478d67bef89f103d323528a5dd33a956831ce21bf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dac91c8d598306dc5bc0c1a478d67bef89f103d323528a5dd33a956831ce21bf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dac91c8d598306dc5bc0c1a478d67bef89f103d323528a5dd33a956831ce21bf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/mcp_unit/assistant_surface_spec.spl
mirror: doc/06_spec/01_unit/app/mcp_unit/assistant_surface_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/mcp_unit/assistant_surface_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/mcp_unit/assistant_surface_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/mcp_unit/assistant_surface_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'publishes the core assistant tools' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/mcp_unit/assistant_surface_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'marks assistant tools as in-process handlers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/mcp_unit/assistant_surface_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires a path for duplicate-check tools' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
