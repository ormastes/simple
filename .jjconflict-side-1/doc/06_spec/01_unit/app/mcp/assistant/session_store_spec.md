# Session Store Specification

> 1. json parse

<!-- sdn-diagram:id=session_store_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=session_store_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

session_store_spec -> std
session_store_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=session_store_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Session Store Specification

## Scenarios

### assistant session store

#### creates, loads, updates, and tracks child metadata

1. json parse
   - Expected: session.session_id equals `assistant-core-1`
   - Expected: session.name equals `Assistant Core`
   - Expected: session.summary equals `build the store`
   - Expected: session.state equals `running`
2. fail
   - Expected: listed.len() equals `1`
3. json parse
   - Expected: session.event_count equals `1`
   - Expected: session.last_event_kind equals `note`
4. fail
   - Expected: session.state equals `paused`
   - Expected: session.event_count equals `2`
   - Expected: session.last_event_kind equals `state`
   - Expected: session.last_signal equals `pause`
5. fail
6. json parse
   - Expected: session.event_count equals `3`
   - Expected: session.last_event_kind equals `child_task`
   - Expected: session.children.len() equals `1`
   - Expected: session.children[0] equals `assistant-child-1`
   - Expected: session.child_tasks.len() equals `1`
   - Expected: session.child_tasks[0].child_session_id equals `assistant-child-1`
7. fail
   - Expected: session.session_id equals `assistant-core-1`
   - Expected: session.state equals `paused`
   - Expected: session.event_count equals `3`
   - Expected: session.children.len() equals `1`
   - Expected: session.child_tasks.len() equals `1`
   - Expected: session.child_tasks[0].child_session_id equals `assistant-child-1`
8. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 64 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = test_root("roundtrip")
val created = assistant_store_create_session(
    root,
    json_parse(r"""{"session_id":"assistant-core-1","name":"Assistant Core","summary":"build the store","objective":"build the store","prompt":"build the store","mode":"proactive","state":"running"}""")
)
match created:
    case Some(session):
        expect(session.session_id).to_equal("assistant-core-1")
        expect(session.name).to_equal("Assistant Core")
        expect(session.summary).to_equal("build the store")
        expect(session.state).to_equal("running")
    case nil:
        fail("assistant session should be created")

val listed = assistant_store_list_sessions(root)
expect(listed.len()).to_equal(1)

val appended = assistant_store_append_event(
    root,
    json_parse(r"""{"session_id":"assistant-core-1","kind":"note","message":"first event","signal":""}""")
)
match appended:
    case Some(session):
        expect(session.event_count).to_equal(1)
        expect(session.last_event_kind).to_equal("note")
    case nil:
        fail("assistant event append should return session")

val updated = assistant_store_update_state(root, "assistant-core-1", "paused", "pause")
match updated:
    case Some(session):
        expect(session.state).to_equal("paused")
        expect(session.event_count).to_equal(2)
        expect(session.last_event_kind).to_equal("state")
        expect(session.last_signal).to_equal("pause")
    case nil:
        fail("assistant state update should return session")

val child = assistant_store_create_child_task(
    root,
    json_parse(r"""{"session_id":"assistant-core-1","objective":"inspect subgraph","owner_kind":"assistant","resource_policy":"bounded","child_session_id":"assistant-child-1","status":"queued"}""")
)
match child:
    case Some(session):
        expect(session.event_count).to_equal(3)
        expect(session.last_event_kind).to_equal("child_task")
        expect(session.children.len()).to_equal(1)
        expect(session.children[0]).to_equal("assistant-child-1")
        expect(session.child_tasks.len()).to_equal(1)
        expect(session.child_tasks[0].child_session_id).to_equal("assistant-child-1")
    case nil:
        fail("assistant child task creation should return session")

val loaded = assistant_store_load_session(root, "assistant-core-1")
match loaded:
    case Some(session):
        expect(session.session_id).to_equal("assistant-core-1")
        expect(session.state).to_equal("paused")
        expect(session.event_count).to_equal(3)
        expect(session.children.len()).to_equal(1)
        expect(session.child_tasks.len()).to_equal(1)
        expect(session.child_tasks[0].child_session_id).to_equal("assistant-child-1")
    case nil:
        fail("assistant session should load after updates")
```

</details>

#### writes dashboard-compatible session and timeline files

1. json parse
   - Expected: session.session_id equals `assistant-core-compat`
2. fail
3. json parse
4. assistant store update state
5. json parse
6. fail
   - Expected: json_to_string(json_object_get(session_value, "id")) equals `assistant-core-compat`
   - Expected: json_to_string(json_object_get(session_value, "state")) equals `running`
   - Expected: json_get_type(json_object_get(session_value, "updated_at")) equals `number`
   - Expected: json_get_type(json_object_get(session_value, "child_tasks")) equals `array`
   - Expected: json_array_length(json_object_get(session_value, "child_tasks")) equals `1`
   - Expected: non_empty_lines_count(timeline_jsonl) equals `3`
7. fail
   - Expected: json_to_string(json_object_get(first_line, "kind")) equals `note`


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = test_root("compat")
val created = assistant_store_create_session(
    root,
    json_parse(r"""{"session_id":"assistant-core-compat","name":"Compat Session","summary":"compatibility","objective":"compatibility","prompt":"compatibility","mode":"proactive","state":"running"}""")
)
match created:
    case Some(session):
        expect(session.session_id).to_equal("assistant-core-compat")
    case nil:
        fail("compat session should be created")

assistant_store_append_event(
    root,
    json_parse(r"""{"session_id":"assistant-core-compat","kind":"note","message":"compat event","signal":""}""")
)
assistant_store_update_state(root, "assistant-core-compat", "running", "resume")
assistant_store_create_child_task(
    root,
    json_parse(r"""{"session_id":"assistant-core-compat","objective":"child compatibility","owner_kind":"assistant","resource_policy":"bounded","child_session_id":"assistant-core-child","status":"queued"}""")
)

val session_json = rt_file_read_text("{root}/sessions/assistant-core-compat.json")
val session_value = json_parse(session_json)
match session_value:
    case nil:
        fail("session JSON should parse")
    case _:
        expect(json_to_string(json_object_get(session_value, "id"))).to_equal("assistant-core-compat")
        expect(json_to_string(json_object_get(session_value, "state"))).to_equal("running")
        expect(json_get_type(json_object_get(session_value, "updated_at"))).to_equal("number")
        expect(json_get_type(json_object_get(session_value, "child_tasks"))).to_equal("array")
        expect(json_array_length(json_object_get(session_value, "child_tasks"))).to_equal(1)

val timeline_jsonl = rt_file_read_text("{root}/timelines/assistant-core-compat.jsonl")
expect(non_empty_lines_count(timeline_jsonl)).to_equal(3)
val first_line = json_parse(timeline_jsonl.split("\n")[0])
match first_line:
    case nil:
        fail("timeline JSONL first line should parse")
    case _:
        expect(json_to_string(json_object_get(first_line, "kind"))).to_equal("note")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp/assistant/session_store_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- assistant session store

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
