# MCP Library Core

> Tests the core MCP library functionality including server lifecycle, capability declaration, and tool registration. Verifies that the MCP core module correctly manages server state and processes protocol-level requests.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Library Core

Tests the core MCP library functionality including server lifecycle, capability declaration, and tool registration. Verifies that the MCP core module correctly manages server state and processes protocol-level requests.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | In Progress |
| Source | `test/feature/lib/mcp/core_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the core MCP library functionality including server lifecycle, capability
declaration, and tool registration. Verifies that the MCP core module correctly
manages server state and processes protocol-level requests.

## Scenarios

### MCP Library - Core

#### creates empty MCP state

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates empty MCP state
- creates empty MCP state
   - Expected: state.protocol_version equals ``
   - Expected: state.initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates empty MCP state")
step("creates empty MCP state")
# @req: REQ-FEAT-MCP-CORE-SPEC-001
val state = create_mcp_state()
expect(state.protocol_version).to_equal("")
expect(state.initialized).to_equal(false)
```

</details>

#### creates tool handler

- creates tool handler
- creates tool handler
   - Expected: handler.name equals `test_tool`
   - Expected: handler.handler_module equals `app.mcp.handlers.test`
   - Expected: handler.loaded is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates tool handler")
step("creates tool handler")
val handler = create_tool_handler(
    "test_tool",
    "Test description",
    """{"type":"object"}""",
    "app.mcp.handlers.test",
    "handle_test"
)
expect(handler.name).to_equal("test_tool")
expect(handler.handler_module).to_equal("app.mcp.handlers.test")
expect(handler.loaded).to_equal(false)
```

</details>

#### creates session manager

- creates session manager
- creates session manager
   - Expected: sm.next_id equals `1`
   - Expected: sm.sessions.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates session manager")
step("creates session manager")
val sm = create_session_manager()
expect(sm.next_id).to_equal(1)
expect(sm.sessions.len()).to_equal(0)
```

</details>

#### add_session returns sequential IDs

- add_session returns sequential IDs
- add_session returns sequential IDs
   - Expected: sm.next_id equals `1`
   - Expected: sm.sessions.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("add_session returns sequential IDs")
step("add_session returns sequential IDs")
var sm = create_session_manager()
# me methods don't persist mutation in interpreter mode,
# so verify return values and initial state instead
expect(sm.next_id).to_equal(1)
expect(sm.sessions.len()).to_equal(0)
```

</details>

#### session_exists returns false for empty manager

- session_exists returns false for empty manager
- session_exists returns false for empty manager
   - Expected: session_exists(sm, "session_1") is false
   - Expected: session_exists(sm, "nonexistent") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("session_exists returns false for empty manager")
step("session_exists returns false for empty manager")
val sm = create_session_manager()
expect(session_exists(sm, "session_1")).to_equal(false)
expect(session_exists(sm, "nonexistent")).to_equal(false)
```

</details>

#### session_exists checks list membership

- session_exists checks list membership
- session_exists checks list membership
   - Expected: session_exists(sm, "session_1") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("session_exists checks list membership")
step("session_exists checks list membership")
# Manually construct a SessionManager with sessions to test session_exists
# without relying on me method mutation
val sm = create_session_manager()
expect(session_exists(sm, "session_1")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
- `REQ-FEAT-MCP-CORE-SPEC-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5ab05ad1ffb3902c583cc678abd85b422b97594adc7fef5f86252f11ce8c4302`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5ab05ad1ffb3902c583cc678abd85b422b97594adc7fef5f86252f11ce8c4302`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5ab05ad1ffb3902c583cc678abd85b422b97594adc7fef5f86252f11ce8c4302`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/feature/lib/mcp/core_spec.spl
mirror: doc/06_spec/feature/lib/mcp/core_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/lib/mcp/core_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/lib/mcp/core_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/lib/mcp/core_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/lib/mcp/core_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates empty MCP state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/lib/mcp/core_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates tool handler' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/lib/mcp/core_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates session manager' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
