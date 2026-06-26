# Session Store Specification

> <details>

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
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Session Store Specification

## Scenarios

### assistant session store

#### rejects non-object root inputs and generates missing session ids

- json parse
   - Expected: session.session_id.starts_with("assistant-") is true
   - Expected: session.name equals `Generated Session`
   - Expected: session.summary equals `generate an id`
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = test_root("input")

expect(assistant_store_create_session(root, json_parse("1"))).to_be_nil()
expect(assistant_store_append_event(root, json_parse("1"))).to_be_nil()
expect(assistant_store_create_child_task(root, json_parse("1"))).to_be_nil()

val created = assistant_store_create_session(
    root,
    json_parse(r"""{"name":"Generated Session","prompt":"generate an id"}""")
)
match created:
    case Some(session):
        expect(session.session_id.starts_with("assistant-")).to_equal(true)
        expect(session.name).to_equal("Generated Session")
        expect(session.summary).to_equal("generate an id")
    case nil:
        fail("valid object session without id should be created")
```

</details>

#### normalizes signal events without hanging and preserves wake reason

- json parse
- json parse
   - Expected: session.last_event_kind equals `signal_event`
   - Expected: session.last_signal equals `wake`
   - Expected: session.last_event_detail equals `wake payload`
   - Expected: session.event_count equals `1`
- fail
   - Expected: session.last_event_kind equals `signal_event`
   - Expected: session.last_signal equals `wake`
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = test_root("signal")
assistant_store_create_session(
    root,
    json_parse(r"""{"session_id":"assistant-signal-1","name":"Signal Session","summary":"signal","objective":"signal","prompt":"signal","mode":"proactive","state":"running"}""")
)

val appended = assistant_store_append_event(
    root,
    json_parse(r"""{"session_id":"assistant-signal-1","kind":"signal","message":"wake payload","signal":"wake","timestamp_ms":1000,"event_id":"event-signal-1"}""")
)
match appended:
    case Some(session):
        expect(session.last_event_kind).to_equal("signal_event")
        expect(session.last_signal).to_equal("wake")
        expect(session.last_event_detail).to_equal("wake payload")
        expect(session.event_count).to_equal(1)
    case nil:
        fail("assistant signal event append should return session")

val loaded = assistant_store_load_session(root, "assistant-signal-1")
match loaded:
    case Some(session):
        expect(session.last_event_kind).to_equal("signal_event")
        expect(session.last_signal).to_equal("wake")
    case nil:
        fail("assistant signal session should load")
```

</details>

#### creates, loads, updates, and tracks child metadata

- json parse
   - Expected: session.session_id equals `assistant-core-1`
   - Expected: session.name equals `Assistant Core`
   - Expected: session.summary equals `build the store`
   - Expected: session.state equals `running`
- fail
   - Expected: listed.len() equals `1`
- json parse
   - Expected: session.event_count equals `1`
   - Expected: session.last_event_kind equals `note`
- fail
   - Expected: session.state equals `paused`
   - Expected: session.event_count equals `2`
   - Expected: session.last_event_kind equals `state`
   - Expected: session.last_signal equals `pause`
- fail
- json parse
   - Expected: session.event_count equals `3`
   - Expected: session.last_event_kind equals `child_task`
   - Expected: session.children.len() equals `1`
   - Expected: session.children[0] equals `assistant-child-1`
   - Expected: session.child_tasks.len() equals `1`
   - Expected: session.child_tasks[0].child_session_id equals `assistant-child-1`
- fail
   - Expected: session.session_id equals `assistant-core-1`
   - Expected: session.state equals `paused`
   - Expected: session.event_count equals `3`
   - Expected: session.children.len() equals `1`
   - Expected: session.child_tasks.len() equals `1`
   - Expected: session.child_tasks[0].child_session_id equals `assistant-child-1`
- fail


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

- json parse
   - Expected: session.session_id equals `assistant-core-compat`
- fail
- json parse
- assistant store update state
- json parse
- fail
   - Expected: json_to_string(json_object_get(session_value, "id")) equals `assistant-core-compat`
   - Expected: json_to_string(json_object_get(session_value, "state")) equals `running`
   - Expected: json_get_type(json_object_get(session_value, "updated_at")) equals `number`
   - Expected: json_get_type(json_object_get(session_value, "child_tasks")) equals `array`
   - Expected: json_array_length(json_object_get(session_value, "child_tasks")) equals `1`
   - Expected: non_empty_lines_count(timeline_jsonl) equals `3`
- fail
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

#### durably prunes timeline and notification jsonl tails while preserving digest checkpoint

- json parse
- json parse
   - Expected: result.status equals `pruned`
   - Expected: result.reason equals `retention_applied`
   - Expected: result.retained_timeline_count equals `3`
   - Expected: result.retained_notification_count equals `2`
   - Expected: result.dropped_timeline_count equals `4`
   - Expected: result.dropped_notification_count equals `5`
   - Expected: result.digest_checkpoint_id equals `digest-keep`
   - Expected: result.evidence.split("nil").len() equals `1`
   - Expected: non_empty_lines_count(timeline_jsonl) equals `3`
   - Expected: non_empty_lines_count(notifications_jsonl) equals `2`
   - Expected: timeline_jsonl.split("event-0").len() equals `1`
   - Expected: session.event_count equals `3`
   - Expected: session.digest_checkpoint_id equals `digest-keep`
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = test_root("retention")
assistant_store_create_session(
    root,
    json_parse(r"""{"session_id":"assistant-retention-core","name":"Retention Core","summary":"retention","objective":"retention","prompt":"retention","mode":"proactive","state":"running","digest_checkpoint_id":"digest-keep"}""")
)
var i: i64 = 0
while i < 7:
    assistant_store_append_event(
        root,
        json_parse("{\"session_id\":\"assistant-retention-core\",\"kind\":\"note\",\"message\":\"event-{i}\",\"signal\":\"\",\"timestamp_ms\":{i},\"event_id\":\"event-{i}\"}")
    )
    i = i + 1

val result = assistant_store_prune_session_retention(root, "assistant-retention-core", 3, 2)

expect(result.status).to_equal("pruned")
expect(result.reason).to_equal("retention_applied")
expect(result.retained_timeline_count).to_equal(3)
expect(result.retained_notification_count).to_equal(2)
expect(result.dropped_timeline_count).to_equal(4)
expect(result.dropped_notification_count).to_equal(5)
expect(result.digest_checkpoint_id).to_equal("digest-keep")
expect(result.evidence.split("nil").len()).to_equal(1)

val timeline_jsonl = rt_file_read_text("{root}/timelines/assistant-retention-core.jsonl")
val notifications_jsonl = rt_file_read_text("{root}/notifications/assistant-retention-core.jsonl")
expect(non_empty_lines_count(timeline_jsonl)).to_equal(3)
expect(non_empty_lines_count(notifications_jsonl)).to_equal(2)
expect(timeline_jsonl).to_contain("event-4")
expect(timeline_jsonl).to_contain("event-6")
expect(timeline_jsonl.split("event-0").len()).to_equal(1)

val loaded = assistant_store_load_session(root, "assistant-retention-core")
match loaded:
    case Some(session):
        expect(session.event_count).to_equal(3)
        expect(session.digest_checkpoint_id).to_equal("digest-keep")
    case nil:
        fail("retained assistant session should load after pruning")
```

</details>

#### generates durable digest checkpoints and prunes old checkpoint entries

- json parse
- json parse
- assistant store update state
   - Expected: first.status equals `generated`
   - Expected: first.reason equals `digest_generated`
   - Expected: first.retained_checkpoint_count equals `1`
   - Expected: first.dropped_checkpoint_count equals `0`
   - Expected: second.status equals `generated`
   - Expected: second.retained_checkpoint_count equals `1`
   - Expected: second.dropped_checkpoint_count equals `1`
   - Expected: second.evidence.split("nil").len() equals `1`
   - Expected: non_empty_lines_count(digest_jsonl) equals `1`
   - Expected: digest_jsonl.split(first.checkpoint_id).len() equals `1`
   - Expected: session.digest_checkpoint_id equals `second.checkpoint_id`
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = test_root("digest")
assistant_store_create_session(
    root,
    json_parse(r"""{"session_id":"assistant-digest-core","name":"Digest Core","summary":"digest","objective":"digest","prompt":"digest","mode":"proactive","state":"running"}""")
)
assistant_store_append_event(
    root,
    json_parse(r"""{"session_id":"assistant-digest-core","kind":"note","message":"first digest event","signal":"","timestamp_ms":1000,"event_id":"digest-event-1"}""")
)
val first = assistant_store_generate_session_digest(root, "assistant-digest-core", 5)
assistant_store_update_state(root, "assistant-digest-core", "running", "resume")
val second = assistant_store_generate_session_digest(root, "assistant-digest-core", 1)

expect(first.status).to_equal("generated")
expect(first.reason).to_equal("digest_generated")
expect(first.retained_checkpoint_count).to_equal(1)
expect(first.dropped_checkpoint_count).to_equal(0)
expect(first.digest_text).to_contain("events=1")
expect(second.status).to_equal("generated")
expect(second.retained_checkpoint_count).to_equal(1)
expect(second.dropped_checkpoint_count).to_equal(1)
expect(second.digest_text).to_contain("recent=resume")
expect(second.evidence.split("nil").len()).to_equal(1)

val digest_jsonl = rt_file_read_text("{root}/digests/assistant-digest-core.jsonl")
expect(non_empty_lines_count(digest_jsonl)).to_equal(1)
expect(digest_jsonl).to_contain(second.checkpoint_id)
expect(digest_jsonl.split(first.checkpoint_id).len()).to_equal(1)

val loaded = assistant_store_load_session(root, "assistant-digest-core")
match loaded:
    case Some(session):
        expect(session.digest_checkpoint_id).to_equal(second.checkpoint_id)
    case nil:
        fail("assistant session should retain generated digest checkpoint id")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp/assistant/session_store_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- assistant session store

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
