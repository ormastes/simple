# Window Event Specification

> Tests covering normalized window event queue.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Window Event Specification

## Scenarios

### normalized window event queue

#### preserves FIFO key and text events with independent modifiers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- preserves FIFO key and text events with independent modifiers
   - Expected: loop.enqueue(key) equals `WINDOW_STATUS_OK`
   - Expected: loop.enqueue_text(7, 2, 11, "c") equals `WINDOW_STATUS_OK`
   - Expected: first.kind equals `WINDOW_EVENT_KEY`
   - Expected: first.modifiers equals `WINDOW_MOD_CTRL`
   - Expected: second.kind equals `WINDOW_EVENT_TEXT`
   - Expected: loop.text_value(second.text_handle) equals `c`
   - Expected: loop.release_text(second.text_handle) equals `WINDOW_STATUS_OK`
   - Expected: loop.release_text(second.text_handle) equals `WINDOW_STATUS_INVALID_HANDLE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves FIFO key and text events with independent modifiers")
var loop = WindowEventLoop.create(4, 2)
val key = window_event_key(7, 1, 10, 67, 46, WINDOW_ACTION_PRESS, WINDOW_MOD_CTRL)
expect(loop.enqueue(key)).to_equal(WINDOW_STATUS_OK)
expect(loop.enqueue_text(7, 2, 11, "c")).to_equal(WINDOW_STATUS_OK)

val first = loop.poll()
val second = loop.poll()
expect(first.kind).to_equal(WINDOW_EVENT_KEY)
expect(first.modifiers).to_equal(WINDOW_MOD_CTRL)
expect(second.kind).to_equal(WINDOW_EVENT_TEXT)
expect(loop.text_value(second.text_handle)).to_equal("c")
expect(loop.release_text(second.text_handle)).to_equal(WINDOW_STATUS_OK)
expect(loop.release_text(second.text_handle)).to_equal(WINDOW_STATUS_INVALID_HANDLE)
```

</details>

#### fails closed on overflow without overwriting queued events

- fails closed on overflow without overwriting queued events
   - Expected: loop.enqueue(first) equals `WINDOW_STATUS_OK`
   - Expected: loop.enqueue(second) equals `WINDOW_STATUS_OVERFLOW`
   - Expected: loop.dropped_event_count equals `1`
   - Expected: loop.poll().key equals `65`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails closed on overflow without overwriting queued events")
var loop = WindowEventLoop.create(1, 1)
val first = window_event_key(1, 1, 10, 65, 30, WINDOW_ACTION_PRESS, 0)
val second = window_event_key(1, 2, 11, 66, 48, WINDOW_ACTION_PRESS, 0)
expect(loop.enqueue(first)).to_equal(WINDOW_STATUS_OK)
expect(loop.enqueue(second)).to_equal(WINDOW_STATUS_OVERFLOW)
expect(loop.dropped_event_count).to_equal(1)
expect(loop.poll().key).to_equal(65)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/io/window_event_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering normalized window event queue.
- normalized window event queue

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e881ce99ece1234ea14d45b034a0034cb232534be5b8ade9d59677fe973be257`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e881ce99ece1234ea14d45b034a0034cb232534be5b8ade9d59677fe973be257`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e881ce99ece1234ea14d45b034a0034cb232534be5b8ade9d59677fe973be257`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/common/io/window_event_spec.spl
mirror: doc/06_spec/01_unit/lib/common/io/window_event_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/io/window_event_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/io/window_event_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/io/window_event_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/io/window_event_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves FIFO key and text events with independent modifiers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/io/window_event_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed on overflow without overwriting queued events' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
