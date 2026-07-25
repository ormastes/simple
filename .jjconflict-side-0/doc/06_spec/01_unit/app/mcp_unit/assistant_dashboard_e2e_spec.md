# Assistant Dashboard E2e Specification

> 1. file delete

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

1. file delete
2. file delete
3. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val token = "assistant_e2e_{rt_getpid()}"
val start_resp = start_assistant(token)
val session_id = find_session_by_prompt("Verify assistant store bridge {token}")

expect(session_id != "").to_equal(true)
expect(start_resp.contains(token)).to_equal(true)

val list_resp = handle_assistant_list_sessions("2", jo1(""))
expect(list_resp.contains(session_id)).to_equal(true)
expect(list_resp.contains(token)).to_equal(true)

val snapshot = collect_assistant_snapshot()
var matched = false
for session in snapshot.sessions:
    if session.session_id == session_id:
        matched = true
expect(matched).to_equal(true)
expect(snapshot.total_sessions).to_be_greater_than(0)

val timeline = collect_assistant_timeline(session_id)
expect(timeline.len()).to_be_greater_than(0)

file_delete(assistant_session_path(session_id))
file_delete(assistant_timeline_path(session_id))
file_delete(assistant_notifications_path(session_id))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/assistant_dashboard_e2e_spec.spl` |
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
