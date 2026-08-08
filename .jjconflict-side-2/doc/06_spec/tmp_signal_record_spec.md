# Tmp Signal Record Specification

> <details>

<!-- sdn-diagram:id=tmp_signal_record_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tmp_signal_record_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tmp_signal_record_spec -> std
tmp_signal_record_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tmp_signal_record_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmp Signal Record Specification

## Scenarios

### signal record

#### appends record signal

- mark
- assistant store create session record
- mark
- var event = AssistantTimelineRecord new
- mark
   - Expected: appended == nil is false
- mark


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "/tmp/simple-signal-record-{rt_time_now_unix_micros()}"
mark("start")
assistant_store_create_session_record(root, AssistantSessionRecord.new("s", "S", "s", "proactive", "", "", "s"))
mark("created")
var event = AssistantTimelineRecord.new("s", "signal_event", "wake payload", "wake")
event.timestamp_ms = 1000
event.event_id = "event-1"
val appended = assistant_store_append_event_record(root, event)
mark("appended")
expect(appended == nil).to_equal(false)
mark("done")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `tmp_signal_record_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- signal record

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
