# Assistant Retention Specification

> <details>

<!-- sdn-diagram:id=assistant_retention_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=assistant_retention_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

assistant_retention_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=assistant_retention_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Assistant Retention Specification

## Scenarios

### assistant dashboard retention

#### keeps bounded tails and reports backpressure without internal absence marker text

- timeline push
- notifications push
- notifications push
- notifications push
- notifications push
   - Expected: projection.retained_timeline_count equals `5`
   - Expected: projection.retained_notification_count equals `3`
   - Expected: projection.dropped_timeline_count equals `3`
   - Expected: projection.dropped_notification_count equals `1`
   - Expected: projection.backpressure_state equals `backpressure`
- expect absence marker hidden
   - Expected: projection.visible_timeline[0].event_id equals `event-3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var timeline: [AssistantTimelineRecord] = []
var i: i64 = 0
while i < 8:
    timeline.push(make_event(i, "state", "state-{i}", ""))
    i = i + 1
var notifications: [AssistantTimelineRecord] = []
notifications.push(make_event(10, "notice", "one", ""))
notifications.push(make_event(11, "notice", "two", ""))
notifications.push(make_event(12, "notice", "three", ""))
notifications.push(make_event(13, "notice", "four", ""))

val projection = assistant_dashboard_retention_projection(make_snapshot(timeline, notifications), tight_policy())

expect(projection.retained_timeline_count).to_equal(5)
expect(projection.retained_notification_count).to_equal(3)
expect(projection.dropped_timeline_count).to_equal(3)
expect(projection.dropped_notification_count).to_equal(1)
expect(projection.backpressure_state).to_equal("backpressure")
expect_absence_marker_hidden(projection.notice)
expect(projection.visible_timeline[0].event_id).to_equal("event-3")
```

</details>

#### coalesces repeated signal and notification bursts

- timeline push
- notifications push
- notifications push
- notifications push
- notifications push
   - Expected: projection.retained_timeline_count equals `2`
   - Expected: projection.retained_notification_count equals `2`
   - Expected: projection.coalesced_signal_count equals `3`
   - Expected: projection.coalesced_notification_count equals `1`
   - Expected: projection.dropped_timeline_count equals `0`
   - Expected: projection.dropped_notification_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var timeline: [AssistantTimelineRecord] = []
var i: i64 = 0
while i < 5:
    timeline.push(make_event(i, "signal_event", "wake", "poke"))
    i = i + 1
var notifications: [AssistantTimelineRecord] = []
notifications.push(make_event(20, "notice", "same", ""))
notifications.push(make_event(21, "notice", "same", ""))
notifications.push(make_event(22, "notice", "same", ""))
notifications.push(make_event(23, "notice", "same", ""))

val projection = assistant_dashboard_retention_projection(make_snapshot(timeline, notifications), tight_policy())

expect(projection.retained_timeline_count).to_equal(2)
expect(projection.retained_notification_count).to_equal(2)
expect(projection.coalesced_signal_count).to_equal(3)
expect(projection.coalesced_notification_count).to_equal(1)
expect(projection.dropped_timeline_count).to_equal(0)
expect(projection.dropped_notification_count).to_equal(1)
expect(projection.notice).to_contain("signals_coalesced=3")
```

</details>

#### stays normal when events fit the retention policy

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val timeline = [make_event(1, "state", "ready", "")]
val notifications = [make_event(2, "notice", "ready", "")]
val projection = assistant_dashboard_retention_projection(make_snapshot(timeline, notifications), tight_policy())

expect(projection.backpressure_state).to_equal("normal")
expect(projection.notice).to_equal("retention normal")
expect(projection.dropped_timeline_count).to_equal(0)
expect(projection.dropped_notification_count).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_dashboard/assistant_retention_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- assistant dashboard retention

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
