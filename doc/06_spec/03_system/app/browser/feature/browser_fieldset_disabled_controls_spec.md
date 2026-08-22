# browser_fieldset_disabled_controls_spec

> Verifies the browser fieldset disabled controls behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# browser_fieldset_disabled_controls_spec

Verifies the browser fieldset disabled controls behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/browser/feature/browser_fieldset_disabled_controls_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the browser fieldset disabled controls behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### BrowserSession disabled fieldset controls

#### should reject disabled fieldset button and text input actions

- Verify: should reject disabled fieldset button and text input actions
- Open disabled controls through the public BrowserSession surface
   - Expected: blocked_buttons.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: inputs.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: blocked_buttons[0].enabled is false
   - Expected: inputs[0].enabled is false
- Route click and text actions through UI access
- Observe no callback, state mutation, or pixel change
   - Expected: clicked.code equals `disabled`
   - Expected: edited.code equals `disabled`
   - Expected: session.dom_callback_count equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: session.current_title equals ``
- Keep the first legend exception interactive
   - Expected: legends.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: legends[0].enabled is true
   - Expected: session.current_title equals `LegendAllowed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 52 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-007 REQ-WEB-BROWSER-008 REQ-WEB-BROWSER-021
step("Verify: should reject disabled fieldset button and text input actions")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Open disabled controls through the public BrowserSession surface")
var session = BrowserSession.new()
expect(session.open_html(
    "https://example.com/fieldset",
    "<html><body><fieldset disabled><button onclick=\"document.title='WrongButton'\">Blocked</button><input value='old' oninput=\"document.title='WrongInput'\"></fieldset><fieldset disabled><legend><button onclick=\"document.title='LegendAllowed'\">Legend</button></legend></fieldset></body></html>"
).is_ok()).to_equal(true)
val pixels_before = session.render_to_pixels(16, 16).pixels
val blocked_buttons = ui_access_find_nodes(
    session.ui_access_snapshot(), "browser:session", "button", "Blocked", 1
)
val inputs = ui_access_find_nodes(
    session.ui_access_snapshot(), "browser:session", "textfield", "old", 1
)
expect(blocked_buttons.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(inputs.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(blocked_buttons[0].enabled).to_equal(false)
expect(inputs[0].enabled).to_equal(false)

step("Route click and text actions through UI access")
val clicked = session.ui_access_act(WinTextActionRequest(
    target_id: blocked_buttons[0].canonical_id, action: "click",
    text_value: "", x: 0, y: 0
))
val edited = session.ui_access_act(WinTextActionRequest(
    target_id: inputs[0].canonical_id, action: "set_value",
    text_value: "new", x: 0, y: 0
))

step("Observe no callback, state mutation, or pixel change")
expect(clicked.code).to_equal("disabled")
expect(edited.code).to_equal("disabled")
expect(session.dom_callback_count).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(session.current_title).to_equal("")
expect(session.current_body_html).to_contain("value=\"old\"")
expect(_pixels_same(
    session.render_to_pixels(16, 16).pixels, pixels_before
)).to_equal(true)

step("Keep the first legend exception interactive")
val legends = ui_access_find_nodes(
    session.ui_access_snapshot(), "browser:session", "button", "Legend", 1
)
expect(legends.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(legends[0].enabled).to_equal(true)
expect(session.ui_access_act(WinTextActionRequest(
    target_id: legends[0].canonical_id, action: "click",
    text_value: "", x: 0, y: 0
)).ok).to_equal(true)
expect(session.current_title).to_equal("LegendAllowed")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `90f9fa80a5e05029224e0defdf88cb7aab06806d2d83934800651a5e6d0e839a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `90f9fa80a5e05029224e0defdf88cb7aab06806d2d83934800651a5e6d0e839a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `90f9fa80a5e05029224e0defdf88cb7aab06806d2d83934800651a5e6d0e839a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/browser/feature/browser_fieldset_disabled_controls_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/browser_fieldset_disabled_controls_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/browser/feature/browser_fieldset_disabled_controls_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/browser/feature/browser_fieldset_disabled_controls_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/browser_fieldset_disabled_controls_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser/feature/browser_fieldset_disabled_controls_spec.spl:36:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject disabled fieldset button and text input actions' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
