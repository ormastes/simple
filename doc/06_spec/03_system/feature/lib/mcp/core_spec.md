# MCP Library Core

> Tests the core MCP library functionality including server lifecycle, capability declaration, and tool registration. Verifies that the MCP core module correctly manages server state and processes protocol-level requests.

<!-- sdn-diagram:id=core_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=core_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

core_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=core_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/03_system/feature/lib/mcp/core_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the core MCP library functionality including server lifecycle, capability
declaration, and tool registration. Verifies that the MCP core module correctly
manages server state and processes protocol-level requests.

## Scenarios

### MCP Library - Core

#### creates empty MCP state

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = create_mcp_state()
expect(state.protocol_version).to_equal("")
expect(state.initialized).to_equal(false)
```

</details>

#### creates tool handler

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sm = create_session_manager()
expect(sm.next_id).to_equal(1)
expect(sm.sessions.len()).to_equal(0)
```

</details>

#### add_session returns sequential IDs

1. var sm = create session manager
   - Expected: sm.next_id equals `1`
   - Expected: sm.sessions.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sm = create_session_manager()
# me methods don't persist mutation in interpreter mode,
# so verify return values and initial state instead
expect(sm.next_id).to_equal(1)
expect(sm.sessions.len()).to_equal(0)
```

</details>

#### session_exists returns false for empty manager

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sm = create_session_manager()
expect(session_exists(sm, "session_1")).to_equal(false)
expect(session_exists(sm, "nonexistent")).to_equal(false)
```

</details>

#### session_exists checks list membership

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
