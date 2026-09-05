# Session Views Specification

> 1. fail

<!-- sdn-diagram:id=session_views_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=session_views_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

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

#### renders detail and compact brief from the file-backed store

1. fail
2. var first = AssistantTimelineRecord new
3. assistant store append event
4. var second = AssistantTimelineRecord new
5. assistant store append event
   - Expected: session.session_id equals `session_id`
   - Expected: session.event_count equals `2`
   - Expected: session.last_event_kind equals `note`
   - Expected: session.last_event_detail equals `second event`
6. fail
   - Expected: brief contains `"session: " + session_id`
   - Expected: brief contains `timeline events: 2`
   - Expected: brief contains `notifications: 2`
   - Expected: brief contains `last event: note - second event`


<details>
<summary>Executable SSpec</summary>

Runnable source: 45 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = test_root("detail")
val session_id = "assistant-views-detail"
val created = assistant_store_create_session(
    root,
    AssistantSessionRecord.new(
        session_id,
        "Assistant Views",
        "build reusable session views",
        "proactive",
        "",
        "",
        "build reusable session views"
    )
)
match created:
    case Some(session):
        expect(session.session_id).to_equal(session_id)
    case nil:
        fail("assistant_store_create_session returned nil")

var first = AssistantTimelineRecord.new(session_id, "note", "first event", "")
first.timestamp_ms = 1000
first.event_id = "event-1"
assistant_store_append_event(root, first)

var second = AssistantTimelineRecord.new(session_id, "note", "second event", "")
second.timestamp_ms = 2000
second.event_id = "event-2"
assistant_store_append_event(root, second)

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

#### collects timeline and notifications from the same persisted files

1. var first = AssistantTimelineRecord new
2. assistant store append event
3. var second = AssistantTimelineRecord new
4. assistant store append event
   - Expected: timeline.len() equals `2`
   - Expected: timeline[0].message equals `first event`
   - Expected: timeline[1].message equals `second event`
   - Expected: timeline_tail.len() equals `1`
   - Expected: timeline_tail[0].message equals `second event`
   - Expected: notifications.len() equals `2`
   - Expected: notifications[0].message equals `first event`
   - Expected: notifications[1].message equals `second event`
   - Expected: notifications_tail.len() equals `1`
   - Expected: notifications_tail[0].message equals `second event`


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = test_root("collect")
val session_id = "assistant-views-collect"
assistant_store_create_session(
    root,
    AssistantSessionRecord.new(
        session_id,
        "Assistant Views Collect",
        "collect view data",
        "proactive",
        "",
        "",
        "collect view data"
    )
)

var first = AssistantTimelineRecord.new(session_id, "note", "first event", "")
first.timestamp_ms = 1000
first.event_id = "event-1"
assistant_store_append_event(root, first)

var second = AssistantTimelineRecord.new(session_id, "signal", "second event", "wake")
second.timestamp_ms = 2000
second.event_id = "event-2"
assistant_store_append_event(root, second)

val timeline = assistant_store_collect_timeline(root, session_id, 10, 0)
expect(timeline.len()).to_equal(2)
expect(timeline[0].message).to_equal("first event")
expect(timeline[1].message).to_equal("second event")

val timeline_tail = assistant_store_collect_timeline(root, session_id, 1, 1500)
expect(timeline_tail.len()).to_equal(1)
expect(timeline_tail[0].message).to_equal("second event")

val notifications = assistant_store_collect_notifications(root, session_id, 10, 0)
expect(notifications.len()).to_equal(2)
expect(notifications[0].message).to_equal("first event")
expect(notifications[1].message).to_equal("second event")

val notifications_tail = assistant_store_collect_notifications(root, session_id, 1, 1500)
expect(notifications_tail.len()).to_equal(1)
expect(notifications_tail[0].message).to_equal("second event")
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
