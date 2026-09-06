# Browser Focus Editability Order Specification

> Tests covering BrowserSession focus editability ordering.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Focus Editability Order Specification

## Scenarios

### BrowserSession focus editability ordering

#### should stop beforeinput when focus makes a text field disabled

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should stop beforeinput when focus makes a text field disabled
- Open an editable field whose focus listener disables it
- Request text mutation through the public UI action
- Observe focus only: no beforeinput callback, mutation, or pixels
   - Expected: result.ok is false
   - Expected: result.code equals `action_failed`
   - Expected: session.dom_callback_count equals `1`
   - Expected: session.current_title equals `Focused`
   - Expected: session.current_body_html does not contain `value="new"`
   - Expected: post_focus.len() equals `1`
   - Expected: post_focus[0].enabled is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should stop beforeinput when focus makes a text field disabled")
step("Open an editable field whose focus listener disables it")
var session = BrowserSession.new()
expect(session.open_html(
    "https://example.com/edit-order",
    "<html><body><input value='old' onfocus=\"set-attr:disabled=disabled;document.title='Focused'\" onbeforeinput=\"document.title='WrongBeforeInput'\"></body></html>"
).is_ok()).to_equal(true)
val pixels_before = session.render_to_pixels(16, 16).pixels

step("Request text mutation through the public UI action")
val inputs = ui_access_find_nodes(
    session.ui_access_snapshot(), "browser:session",
    "textfield", "old", 1
)
val result = session.ui_access_act(WinTextActionRequest(
    target_id: inputs[0].canonical_id, action: "set_value",
    text_value: "new", x: 0, y: 0
))

step("Observe focus only: no beforeinput callback, mutation, or pixels")
expect(result.ok).to_equal(false)
expect(result.code).to_equal("action_failed")
expect(session.dom_callback_count).to_equal(1)
expect(session.current_title).to_equal("Focused")
expect(session.current_body_html).to_contain("value=\"old\"")
expect(session.current_body_html.contains("value=\"new\"")).to_equal(false)
val post_focus = ui_access_find_nodes(
    session.ui_access_snapshot(), "browser:session", "textfield", "old", 1
)
expect(post_focus.len()).to_equal(1)
expect(post_focus[0].enabled).to_equal(false)
expect(_pixels_same(
    session.render_to_pixels(16, 16).pixels, pixels_before
)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/browser/feature/browser_focus_editability_order_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BrowserSession focus editability ordering.
- BrowserSession focus editability ordering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2c4a8394807cbfc3a65ee9edeec3541fa9fdd42a9e99943e436cc17bbfe3091d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2c4a8394807cbfc3a65ee9edeec3541fa9fdd42a9e99943e436cc17bbfe3091d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2c4a8394807cbfc3a65ee9edeec3541fa9fdd42a9e99943e436cc17bbfe3091d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/app/browser/feature/browser_focus_editability_order_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/browser_focus_editability_order_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=95 oracle=80
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/browser/feature/browser_focus_editability_order_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/browser_focus_editability_order_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser/feature/browser_focus_editability_order_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/browser/feature/browser_focus_editability_order_spec.spl:27:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should stop beforeinput when focus makes a text field disabled' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/browser/feature/browser_focus_editability_order_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should stop beforeinput when focus makes a text field disabled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
