# Winit Ordered Committed Text Specification

> Tests covering ordered Winit committed-text delivery.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Winit Ordered Committed Text Specification

## Scenarios

### ordered Winit committed-text delivery

#### owned native records

#### copies text before freeing and derives compatibility kinds

- copies text before freeing and derives compatibility kinds


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("copies text before freeing and derives compatibility kinds")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val source = file_read(WINT)
val record = file_read(EVENT_RECORD)
val runtime = file_read(RUNTIME)
expect(record).to_contain("struct WinitInputEvent:")
expect(record).to_contain("keycode: i64")
expect(record).to_contain("pressed: bool")
expect(record).to_contain("committed_text: text")
expect(record).to_contain("mut events_out: [WinitInputEvent]")
expect(record).to_contain("events_out.push(event)")
expect(record).to_contain("event_kinds_out.push(event.kind)")
expect(source).to_contain(
    "val committed_text = if kind == EVT_TEXT:")
expect(source).to_contain("winit_poll_input_into(")
expect(source).to_contain("winit_wait_input_into(")
expect(source).to_contain(
    "events_out, event_kinds, kind, keycode, pressed, committed_text)")
expect(source).to_contain(
    "kind == EVT_KEYBOARD or kind == EVT_TEXT")
expect(source).to_contain("rt_winit_event_free(ev)")
expect(runtime).to_contain("origin_keycode: i64")
expect(runtime).to_contain("origin_pressed: bool")
expect(runtime).to_contain("origin_keycode,")
expect(runtime).to_contain("origin_pressed,")
expect(runtime).to_contain("origin_keycode: 0")
expect(runtime).to_contain("origin_pressed: false")
expect(runtime).to_contain(
    "StoredEvent::Text { origin_keycode, .. }")
expect(runtime).to_contain(
    "StoredEvent::Text { origin_pressed, .. }")
expect(source.contains(
    "    events: [WinitInputEvent]")).to_equal(false)
```

</details>

#### web event reduction

#### uses each record's text and admits one visible committed g

- uses each record's text and admits one visible committed g


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("uses each record's text and admits one visible committed g")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val source = file_read(WEB)
expect(source).to_contain(
    "var input_events: [WinitInputEvent] = []")
expect(source).to_contain(
    "winit_poll_input_into(lp, input_events)")
expect(source).to_contain("for event in input_events:")
expect(source).to_contain("val raw_kind = event.kind")
expect(source).to_contain(
    "raw_kind == 11 and event.committed_text != \"\"")
expect(source).to_contain(
    "event.committed_text == \"g\"")
expect(source).to_contain(
    "committed_text_receipt_revision == 0")
expect(source).to_contain(
    "committed_text_revision > keyboard_revision")
expect(source).to_contain("committed_text_events == 1")
expect(source).to_contain(
    "INPUT \" + committed_text + \" REV ")
expect(source.contains(
    "for raw_kind in input.event_kinds:")).to_equal(false)
```

</details>

#### requires the committed record and revision in live evidence

- requires the committed record and revision in live evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("requires the committed record and revision in live evidence")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val source = file_read(WRAPPER)
expect(source).to_contain("keystroke \"g\"")
expect(source).to_contain(
    "web_standards_event_committed_text")
expect(source).to_contain(
    "committed-text-duplicate-or-missing")
expect(source).to_contain(
    "keyboard_revision\" -lt \"$committed_text_revision")
expect(source).to_contain(
    "macos_vulkan_web_live_committed_text_receipt_revision")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/winit_ordered_committed_text_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ordered Winit committed-text delivery.
- ordered Winit committed-text delivery

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1f16f7974e0c0e1c1d5b178547a0d1ea75c139e3e0ee097257d5b8186737d413`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1f16f7974e0c0e1c1d5b178547a0d1ea75c139e3e0ee097257d5b8186737d413`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1f16f7974e0c0e1c1d5b178547a0d1ea75c139e3e0ee097257d5b8186737d413`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/02_integration/rendering/winit_ordered_committed_text_spec.spl
mirror: doc/06_spec/02_integration/rendering/winit_ordered_committed_text_spec.md (current)
findings: 3 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=87; blocker cap makes effective=49
doc/06_spec/02_integration/rendering/winit_ordered_committed_text_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/rendering/winit_ordered_committed_text_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/rendering/winit_ordered_committed_text_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
<!-- sspec-maintain:scorecard:end -->
