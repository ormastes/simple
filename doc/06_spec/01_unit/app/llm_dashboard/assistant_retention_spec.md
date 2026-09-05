# Assistant Retention Specification

> Tests covering assistant dashboard retention.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Assistant Retention Specification

## Scenarios

### assistant dashboard retention

#### keeps bounded tails and reports backpressure without internal absence marker text

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps bounded tails and reports backpressure without internal absence marker text
   - Expected: projection.retained_timeline_count equals `5`
   - Expected: projection.retained_notification_count equals `3`
   - Expected: projection.dropped_timeline_count equals `3`
   - Expected: projection.dropped_notification_count equals `1`
   - Expected: projection.backpressure_state equals `backpressure`
   - Expected: projection.visible_timeline[0].event_id equals `event-3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps bounded tails and reports backpressure without internal absence marker text")
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

- coalesces repeated signal and notification bursts
   - Expected: projection.retained_timeline_count equals `2`
   - Expected: projection.retained_notification_count equals `2`
   - Expected: projection.coalesced_signal_count equals `3`
   - Expected: projection.coalesced_notification_count equals `1`
   - Expected: projection.dropped_timeline_count equals `0`
   - Expected: projection.dropped_notification_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("coalesces repeated signal and notification bursts")
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

- stays normal when events fit the retention policy
   - Expected: projection.backpressure_state equals `normal`
   - Expected: projection.notice equals `retention normal`
   - Expected: projection.dropped_timeline_count equals `0`
   - Expected: projection.dropped_notification_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("stays normal when events fit the retention policy")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering assistant dashboard retention.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `56a5e4bd613e88a17cc3c7d42a10c95df1eccb00d8f3d7f73dd1b1abe7b20a3f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `56a5e4bd613e88a17cc3c7d42a10c95df1eccb00d8f3d7f73dd1b1abe7b20a3f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `56a5e4bd613e88a17cc3c7d42a10c95df1eccb00d8f3d7f73dd1b1abe7b20a3f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/app/llm_dashboard/assistant_retention_spec.spl
mirror: doc/06_spec/01_unit/app/llm_dashboard/assistant_retention_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/llm_dashboard/assistant_retention_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_dashboard/assistant_retention_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_dashboard/assistant_retention_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/llm_dashboard/assistant_retention_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps bounded tails and reports backpressure without internal absence marker text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_dashboard/assistant_retention_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'coalesces repeated signal and notification bursts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_dashboard/assistant_retention_spec.spl:114:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stays normal when events fit the retention policy' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
