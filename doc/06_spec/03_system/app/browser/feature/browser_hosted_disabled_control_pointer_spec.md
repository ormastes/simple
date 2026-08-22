# Hosted disabled-control pointer suppression

> Verifies the browser hosted disabled control pointer behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hosted disabled-control pointer suppression

Verifies the browser hosted disabled control pointer behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/browser/feature/browser_hosted_disabled_control_pointer_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the browser hosted disabled control pointer behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Hosted disabled-control pointer suppression

#### should suppress disabled fieldset controls and preserve the first legend exception

- Verify: should suppress disabled fieldset controls and preserve the first legend exception
   - GUI capture: after_step (HTML preferred when available)
- Open fixed hosted controls and capture the initial frame
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 1 expected check
   - Expected: session.failure_reason equals ``
- Press and release disabled fieldset controls
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 4 expected checks
   - Expected: button_down.semantic_target_id equals `blocked-child`
   - Expected: button_up.semantic_target_id equals `blocked-child`
   - Expected: checkbox_down.semantic_target_id equals `blocked-check`
   - Expected: checkbox_up.semantic_target_id equals `blocked-check`
- Observe no listener state checked state or pixel change
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 7 expected checks
   - Expected: button_down.callback_count equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: button_up.callback_count equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: checkbox_down.callback_count equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: checkbox_up.callback_count equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: session.browser.dom_callback_count equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: session.browser.current_title equals ``
   - Expected: session.current_body_html() equals `initial_body`
- Activate the first legend exception
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 8 expected checks
   - Expected: legend_down.semantic_target_id equals `legend-button`
   - Expected: legend_up.semantic_target_id equals `legend-button`
   - Expected: legend_up.callback_count equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: session.browser.dom_callback_count equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: session.browser.current_title equals `LegendAllowed`
   - Expected: scripted.actions.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: session.browser.dom_callback_count equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: session.browser.current_title equals `WrongButton`


<details>
<summary>Executable SSpec</summary>

Runnable source: 121 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-007 REQ-WEB-BROWSER-008 REQ-WEB-BROWSER-021
step("Verify: should suppress disabled fieldset controls and preserve the first legend exception")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Open fixed hosted controls and capture the initial frame")
var session = HostedWebContentSession.create(
    DISABLED_POINTER_WINDOW_ID,
    "<style>body,fieldset,legend{margin:0;padding:0;border:0}" +
    "#legend-button,#blocked-button,#blocked-check{" +
    "position:absolute;margin:0;padding:0;border:0;" +
    "width:40px;height:16px;background-color:#0000ff}" +
    "#legend-button{left:0;top:0}" +
    "#blocked-button{left:0;top:20px}" +
    "#blocked-check{left:0;top:40px}" +
    "#blocked-child{display:block;width:40px;height:16px}" +
    "#blocked-check[checked]{{background-color:#ff0000}}</style>" +
    "<fieldset disabled><legend><button id='legend-button' " +
    "onclick=\"this.style.backgroundColor='#00ff00';" +
    "document.title='LegendAllowed'\">Legend</button></legend>" +
    "<button id='blocked-button' disabled><span id='blocked-child' onclick=\"" +
    "this.setAttribute('data-fired','yes');" +
    "document.title='WrongButton'\">Blocked</span></button>" +
    "<input id='blocked-check' type='checkbox' onclick=\"" +
    "this.setAttribute('data-fired','yes');" +
    "document.title='WrongCheckbox'></fieldset>" +
    "<fieldset disabled style='display:none'><fieldset disabled>" +
    "<legend><button id='nested-legend-button'>Nested</button>" +
    "</legend></fieldset></fieldset>" +
    "<fieldset disabled style='display:none'><label " +
    "id='boundary-label'><input id='boundary-check' " +
    "type='checkbox'></label></fieldset>",
    48, 60
)
val initial_body = session.current_body_html()
val initial_pixels = session.render_to_pixels()
expect(session.failure_reason).to_equal("")
expect(disabled_pointer_color_count(
    initial_pixels, 0xFF0000FFu32
)).to_be_greater_than(0)
val identity_index = system_browser_dom_identity_index(session.browser)
expect(be_dom_control_is_effectively_disabled(
    session.browser.dom_root(), identity_index,
    system_dom_route(identity_index, "legend-button")
)).to_be(false)
expect(be_dom_control_is_effectively_disabled(
    session.browser.dom_root(), identity_index,
    system_dom_route(identity_index, "blocked-child")
)).to_be(true)
expect(be_dom_control_is_effectively_disabled(
    session.browser.dom_root(), identity_index,
    system_dom_route(identity_index, "nested-legend-button")
)).to_be(true)
expect(be_dom_control_is_effectively_disabled(
    session.browser.dom_root(), identity_index,
    system_dom_route(identity_index, "boundary-label")
)).to_be(false)
expect(be_dom_control_is_effectively_disabled(
    session.browser.dom_root(), identity_index,
    system_dom_route(identity_index, "boundary-check")
)).to_be(true)

step("Press and release disabled fieldset controls")
val button_down = session.dispatch_pointer_at(1, 4, 24, true)
val button_up = session.dispatch_pointer_at(2, 4, 24, false)
val checkbox_down = session.dispatch_pointer_at(3, 4, 44, true)
val checkbox_up = session.dispatch_pointer_at(4, 4, 44, false)
expect(button_down.semantic_target_id).to_equal("blocked-child")
expect(button_up.semantic_target_id).to_equal("blocked-child")
expect(checkbox_down.semantic_target_id).to_equal("blocked-check")
expect(checkbox_up.semantic_target_id).to_equal("blocked-check")

step("Observe no listener state checked state or pixel change")
expect(button_down.callback_count).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(button_up.callback_count).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(checkbox_down.callback_count).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(checkbox_up.callback_count).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(session.browser.dom_callback_count).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(session.browser.current_title).to_equal("")
expect(disabled_pointer_has_attr(
    session, "blocked-child", "data-fired"
)).to_be(false)
expect(disabled_pointer_has_attr(
    session, "blocked-button", "data-focused"
)).to_be(false)
expect(disabled_pointer_has_attr(
    session, "blocked-check", "data-fired"
)).to_be(false)
expect(disabled_pointer_has_attr(
    session, "blocked-check", "checked"
)).to_be(false)
expect(session.current_body_html()).to_equal(initial_body)
expect(disabled_pointer_pixels_equal(
    session.render_to_pixels(), initial_pixels
)).to_be(true)

step("Activate the first legend exception")
val legend_down = session.dispatch_pointer_at(5, 4, 4, true)
val legend_up = session.dispatch_pointer_at(6, 4, 4, false)
val legend_pixels = session.render_to_pixels()
expect(legend_down.semantic_target_id).to_equal("legend-button")
expect(legend_up.semantic_target_id).to_equal("legend-button")
expect(legend_up.callback_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(session.browser.dom_callback_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(session.browser.current_title).to_equal("LegendAllowed")
expect(disabled_pointer_attr(
    session, "legend-button", "style"
)).to_contain("background-color")
expect(disabled_pointer_color_count(
    legend_pixels, 0xFF00FF00u32
)).to_be_greater_than(0)
expect(disabled_pointer_pixels_equal(
    legend_pixels, initial_pixels
)).to_be(false)
val scripted = session.browser.dispatch_dom_event(
    "blocked-child", "click", true, true
)
expect(scripted.actions.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(session.browser.dom_callback_count).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(session.browser.current_title).to_equal("WrongButton")
expect(disabled_pointer_attr(
    session, "blocked-child", "data-fired"
)).to_equal("yes")
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

- Canonical SPipe generation for source `1340d647d88bfc235a5fcb0233dc38b07451e94c02679b081bb79ff0feda4dc8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1340d647d88bfc235a5fcb0233dc38b07451e94c02679b081bb79ff0feda4dc8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1340d647d88bfc235a5fcb0233dc38b07451e94c02679b081bb79ff0feda4dc8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/browser/feature/browser_hosted_disabled_control_pointer_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/browser_hosted_disabled_control_pointer_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/browser/feature/browser_hosted_disabled_control_pointer_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/browser/feature/browser_hosted_disabled_control_pointer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/browser_hosted_disabled_control_pointer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser/feature/browser_hosted_disabled_control_pointer_spec.spl:78:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should suppress disabled fieldset controls and preserve the first legend exception' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
