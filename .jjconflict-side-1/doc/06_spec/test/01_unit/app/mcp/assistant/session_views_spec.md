# Session Views Specification

> <details>

<!-- sdn-diagram:id=session_views_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=session_views_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

session_views_spec -> std
session_views_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=session_views_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Session Views Specification

## Scenarios

### assistant session views

#### collects timeline and notifications from the same persisted files

- json parse
- assistant store append event
- assistant store append event
   - Expected: timeline.len() equals `2`
   - Expected: timeline[0].message equals `first event`
   - Expected: timeline[1].message equals `second event`
   - Expected: timeline_tail.len() equals `1`
   - Expected: timeline_tail[0].message equals `second event`
   - Expected: timeline_tail[0].kind equals `signal_event`
   - Expected: timeline_tail[0].signal equals `wake`
   - Expected: notifications.len() equals `2`
   - Expected: notifications[0].message equals `first event`
   - Expected: notifications[1].message equals `second event`
   - Expected: notifications_tail.len() equals `1`
   - Expected: notifications_tail[0].message equals `second event`
   - Expected: notifications_tail[0].kind equals `signal_event`
   - Expected: notifications_tail[0].signal equals `wake`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = test_root("collect")
val session_id = "assistant-views-collect"
assistant_store_create_session(
    root,
    json_parse(r"""{"session_id":"assistant-views-collect","name":"Assistant Views Collect","summary":"collect view data","objective":"collect view data","prompt":"collect view data","mode":"proactive","state":"running"}""")
)

assistant_store_append_event(root, json_parse(r"""{"session_id":"assistant-views-collect","kind":"note","message":"first event","timestamp_ms":1000,"event_id":"event-1"}"""))
assistant_store_append_event(root, json_parse(r"""{"session_id":"assistant-views-collect","kind":"signal","message":"second event","signal":"wake","timestamp_ms":2000,"event_id":"event-2"}"""))

val timeline = assistant_store_collect_timeline(root, session_id, 10, 0)
expect(timeline.len()).to_equal(2)
expect(timeline[0].message).to_equal("first event")
expect(timeline[1].message).to_equal("second event")

val timeline_tail = assistant_store_collect_timeline(root, session_id, 1, 1500)
expect(timeline_tail.len()).to_equal(1)
expect(timeline_tail[0].message).to_equal("second event")
expect(timeline_tail[0].kind).to_equal("signal_event")
expect(timeline_tail[0].signal).to_equal("wake")

val notifications = assistant_store_collect_notifications(root, session_id, 10, 0)
expect(notifications.len()).to_equal(2)
expect(notifications[0].message).to_equal("first event")
expect(notifications[1].message).to_equal("second event")

val notifications_tail = assistant_store_collect_notifications(root, session_id, 1, 1500)
expect(notifications_tail.len()).to_equal(1)
expect(notifications_tail[0].message).to_equal("second event")
expect(notifications_tail[0].kind).to_equal("signal_event")
expect(notifications_tail[0].signal).to_equal("wake")
```

</details>

#### renders detail and compact brief from the file-backed store

- json parse
   - Expected: session.session_id equals `session_id`
- fail
- assistant store append event
- assistant store append event
   - Expected: session.session_id equals `session_id`
   - Expected: session.event_count equals `2`
   - Expected: session.last_event_kind equals `note`
   - Expected: session.last_event_detail equals `second event`
- fail
   - Expected: brief contains `"session: " + session_id`
   - Expected: brief contains `timeline events: 2`
   - Expected: brief contains `notifications: 2`
   - Expected: brief contains `last event: note - second event`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = test_root("detail")
val session_id = "assistant-views-detail"
val created = assistant_store_create_session(
    root,
    json_parse(r"""{"session_id":"assistant-views-detail","name":"Assistant Views","summary":"build reusable session views","objective":"build reusable session views","prompt":"build reusable session views","mode":"proactive","state":"running"}""")
)
match created:
    case Some(session):
        expect(session.session_id).to_equal(session_id)
    case nil:
        fail("assistant_store_create_session returned nil")

assistant_store_append_event(root, json_parse(r"""{"session_id":"assistant-views-detail","kind":"note","message":"first event","timestamp_ms":1000,"event_id":"event-1"}"""))
assistant_store_append_event(root, json_parse(r"""{"session_id":"assistant-views-detail","kind":"note","message":"second event","timestamp_ms":2000,"event_id":"event-2"}"""))

val detail = assistant_store_session_detail(root, session_id)
match detail:
    case Some(session):
        expect(session.session_id).to_equal(session_id)
        expect(session.event_count).to_equal(2)
        expect(session.last_event_kind).to_equal("note")
        expect(session.last_event_detail).to_equal("second event")
    case nil:
        fail("assistant_store_session_detail returned nil")

val brief = assistant_store_session_brief(root, session_id)
expect(brief.contains("session: " + session_id)).to_equal(true)
expect(brief.contains("timeline events: 2")).to_equal(true)
expect(brief.contains("notifications: 2")).to_equal(true)
expect(brief.contains("last event: note - second event")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp/assistant/session_views_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- assistant session views

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
