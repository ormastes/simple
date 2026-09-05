# Assistant Dashboard E2e Specification

> <details>

<!-- sdn-diagram:id=assistant_dashboard_e2e_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=assistant_dashboard_e2e_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

assistant_dashboard_e2e_spec -> app
assistant_dashboard_e2e_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=assistant_dashboard_e2e_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Assistant Dashboard E2e Specification

## Scenarios

### assistant MCP to dashboard e2e

#### starts a session, lists it, and the dashboard reads the stored timeline

- Start an assistant session through the MCP handler.
- List MCP assistant sessions and verify the new session is visible.
- Push a wake signal and require a successful MCP response.
- Collect the dashboard snapshot from persisted assistant store files.
- Read the dashboard timeline and verify the persisted signal event.
- Remove the fixture session, timeline, and notification files.


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val token = "assistant_e2e_{rt_getpid()}"
val start_resp = start_assistant(token)
val session_id = find_session_by_prompt("Verify assistant store bridge {token}")

expect(session_id == "").to_be(false)
expect(start_resp.contains(token)).to_be(true)

val list_resp = handle_assistant_list_sessions("2", jo1(""))
expect(list_resp.contains(session_id)).to_be(true)
expect(list_resp.contains(token)).to_be(true)

val signal_resp = push_wake_signal(session_id)
expect(signal_resp.contains("\"status\":\"ok\"")).to_be(true)

val snapshot = collect_assistant_snapshot()
var matched = false
for session in snapshot.sessions:
    if session.session_id == session_id:
        matched = true
expect(matched).to_be(true)
expect(snapshot.total_sessions).to_be_greater_than(0)

val timeline = collect_assistant_timeline(session_id)
expect(timeline.len()).to_be_greater_than(0)
var signal_found = false
for event in timeline:
    if event.kind == "signal_event" and event.signal == "wake":
        signal_found = true
expect(signal_found).to_be(true)

cleanup_assistant_e2e_session(session_id)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/assistant_dashboard_e2e_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- assistant MCP to dashboard e2e

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
