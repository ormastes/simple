# Session Views Specification

> Tests covering assistant session views.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Session Views Specification

## Scenarios

### assistant session views

#### collects timeline and notifications from the same persisted files

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- collects timeline and notifications from the same persisted files
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

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("collects timeline and notifications from the same persisted files")
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

- renders detail and compact brief from the file-backed store
   - Expected: session.session_id equals `session_id`
   - Expected: session.session_id equals `session_id`
   - Expected: session.event_count equals `2`
   - Expected: session.last_event_kind equals `note`
   - Expected: session.last_event_detail equals `second event`
   - Expected: brief contains `"session: " + session_id`
   - Expected: brief contains `timeline events: 2`
   - Expected: brief contains `notifications: 2`
   - Expected: brief contains `last event: note - second event`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders detail and compact brief from the file-backed store")
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
| Source | `test/unit/app/mcp/assistant/session_views_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering assistant session views.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3c16a761e580038d7f5804d79cc7b37552d07009cc690f9a977723cce76f8460`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3c16a761e580038d7f5804d79cc7b37552d07009cc690f9a977723cce76f8460`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3c16a761e580038d7f5804d79cc7b37552d07009cc690f9a977723cce76f8460`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/app/mcp/assistant/session_views_spec.spl
mirror: doc/06_spec/unit/app/mcp/assistant/session_views_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp/assistant/session_views_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp/assistant/session_views_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp/assistant/session_views_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/mcp/assistant/session_views_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'collects timeline and notifications from the same persisted files' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp/assistant/session_views_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders detail and compact brief from the file-backed store' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
