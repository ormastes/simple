# Session Extended Specification

> <details>

<!-- sdn-diagram:id=session_extended_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=session_extended_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

session_extended_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=session_extended_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Session Extended Specification

## Scenarios

### SessionExtended

#### defines breakpoint lifecycle state transitions and missing-session behavior

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = mcp_session_extended_source()

expect(src).to_contain("class SessionBreakpoint:")
expect(src).to_contain("static fn at_line(id: Int, file: String, line: Int) -> SessionBreakpoint:")
expect(src).to_contain("enabled: true")
expect(src).to_contain("hit_count: 0")
expect(src).to_contain("me add_breakpoint(session_id: String, file: String, line: Int) -> Option<Int>:")
expect(src).to_contain("session.breakpoints.push(bp)")
expect(src).to_contain("case nil:")
expect(src).to_contain("fn remove_breakpoint(session_id: String, bp_id: Int) -> Bool:")
expect(src).to_contain("session.breakpoints = session.breakpoints.filter(_1.id != bp_id)")
expect(src).to_contain("me set_state(session_id: String, new_state: SessionState):")
expect(src).to_contain("session.state = new_state")
```

</details>

#### defines MCP protocol progress cancellation subscription and log state

<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = mcp_session_extended_source()

expect(src).to_contain("class McpState:")
expect(src).to_contain("progress_tokens: Dict<String, String>")
expect(src).to_contain("cancelled_requests: Dict<String, String>")
expect(src).to_contain("in_flight: Dict<String, String>")
expect(src).to_contain("subscriptions: Dict<String, Bool>")
expect(src).to_contain("log_level: Int")
expect(src).to_contain("me register_progress_token(token: String, request_id: String):")
expect(src).to_contain("me register_request(request_id: String, method: String):")
expect(src).to_contain("me cancel_request(request_id: String, reason: String):")
expect(src).to_contain("me subscribe(uri: String):")
expect(src).to_contain("fn should_emit_log(msg_level: Int) -> Bool:")
expect(src).to_contain("me next_server_request_id() -> String:")
expect(src).to_contain("self.next_request_id = self.next_request_id + 1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/session_extended_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SessionExtended

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
