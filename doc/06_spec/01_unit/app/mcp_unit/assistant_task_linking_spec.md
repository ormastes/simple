# Assistant Task Linking Specification

> 1. fail

<!-- sdn-diagram:id=assistant_task_linking_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=assistant_task_linking_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

assistant_task_linking_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=assistant_task_linking_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Assistant Task Linking Specification

## Scenarios

### assistant task linking

#### records child task state on the parent and lists structured child tasks

1. fail
   - Expected: tasks_result contains `assistant`
   - Expected: tasks_result contains `child_task`
   - Expected: tasks_result contains `child_session_id`
   - Expected: tasks_result contains `parent_session_id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stamp = rt_time_now_unix_micros().to_text()
val parent_session_id = "assistant-parent-" + stamp
val child_session_id = "assistant-child-" + stamp
val parent_prompt = "assistant-parent-prompt-" + stamp
val child_prompt = "assistant-child-prompt-" + stamp

val start_body = "{\"session_id\":\"{parent_session_id}\",\"name\":\"assistant_start\",\"prompt\":\"{parent_prompt}\"}"
val start_result = handle_assistant_start("1", start_body)
expect(start_result.contains(parent_prompt)).to_equal(true)

val spawn_body = "{\"session_id\":\"{child_session_id}\",\"parent_session_id\":\"{parent_session_id}\",\"name\":\"assistant_spawn\",\"prompt\":\"{child_prompt}\",\"mode\":\"child-task\"}"
val spawn_result = handle_assistant_spawn_task("2", spawn_body)
expect(spawn_result.contains(child_prompt)).to_equal(true)

val parent = assistant_store_load_session(ASSIST_ROOT, parent_session_id)
match parent:
    case Some(session):
        expect(session.children.len()).to_equal(1)
        expect(session.children[0]).to_equal(child_session_id)
        expect(session.child_tasks.len()).to_equal(1)
        expect(session.child_tasks[0].child_session_id).to_equal(child_session_id)
        expect(session.child_tasks[0].status).to_equal("running")
    case nil:
        fail("parent assistant session was not saved")

val tasks_result = handle_assistant_list_tasks("3", "{\"source\":\"assistant\",\"session_id\":\"{parent_session_id}\"}")
expect(tasks_result.contains("assistant")).to_equal(true)
expect(tasks_result.contains("child_task")).to_equal(true)
expect(tasks_result.contains(child_session_id)).to_equal(true)
expect(tasks_result.contains(parent_session_id)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/assistant_task_linking_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- assistant task linking

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
