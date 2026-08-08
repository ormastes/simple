# Tmp View Full Marker Specification

> <details>

<!-- sdn-diagram:id=tmp_view_full_marker_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tmp_view_full_marker_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tmp_view_full_marker_spec -> std
tmp_view_full_marker_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tmp_view_full_marker_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmp View Full Marker Specification

## Scenarios

### full marker

#### first

- mark
- assistant store create session
- assistant store append event
- assistant store append event
- mark
- mark
   - Expected: session.event_count equals `2`
- mark
   - Expected: session.last_event_kind equals `note`
- mark
   - Expected: session.last_event_detail equals `second event`
- mark
- fail
- mark
   - Expected: brief contains `"session: " + session_id`
- mark
   - Expected: brief contains `timeline events: 2`
- mark
   - Expected: brief contains `notifications: 2`
- mark
   - Expected: brief contains `last event: note - second event`
- mark


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "/tmp/simple-view-full-a-{rt_time_now_unix_micros()}"
val session_id = "assistant-views-detail"
mark("first-start")
assistant_store_create_session(root, json_parse(r"""{"session_id":"assistant-views-detail","name":"Assistant Views","summary":"build reusable session views","objective":"build reusable session views","prompt":"build reusable session views","mode":"proactive","state":"running"}"""))
assistant_store_append_event(root, json_parse(r"""{"session_id":"assistant-views-detail","kind":"note","message":"first event","timestamp_ms":1000,"event_id":"event-1"}"""))
assistant_store_append_event(root, json_parse(r"""{"session_id":"assistant-views-detail","kind":"note","message":"second event","timestamp_ms":2000,"event_id":"event-2"}"""))
mark("first-appended")
val detail = assistant_store_session_detail(root, session_id)
match detail:
    case Some(session):
        mark("detail:" + str(session.event_count) + ":" + session.last_event_kind + ":" + session.last_event_detail)
        expect(session.event_count).to_equal(2)
        mark("detail-count-ok")
        expect(session.last_event_kind).to_equal("note")
        mark("detail-kind-ok")
        expect(session.last_event_detail).to_equal("second event")
        mark("detail-detail-ok")
    case nil:
        fail("nil detail")
val brief = assistant_store_session_brief(root, session_id)
mark("brief:" + brief.replace("\n", "|"))
expect(brief.contains("session: " + session_id)).to_equal(true)
mark("brief-session-ok")
expect(brief.contains("timeline events: 2")).to_equal(true)
mark("brief-timeline-ok")
expect(brief.contains("notifications: 2")).to_equal(true)
mark("brief-notifications-ok")
expect(brief.contains("last event: note - second event")).to_equal(true)
mark("first-done")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `tmp_view_full_marker_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- full marker

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
