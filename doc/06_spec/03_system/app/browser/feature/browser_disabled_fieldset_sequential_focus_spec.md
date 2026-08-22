# Hosted disabled-fieldset sequential focus

> Verifies the browser disabled fieldset sequential focus behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hosted disabled-fieldset sequential focus

Verifies the browser disabled fieldset sequential focus behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/browser/feature/browser_disabled_fieldset_sequential_focus_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the browser disabled fieldset sequential focus behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Hosted disabled-fieldset sequential focus

#### should skip disabled controls and preserve the first legend exception

**Manual warnings:**
- invalid capture metadata value: draw_ir (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Verify: should skip disabled controls and preserve the first legend exception
   - HTML capture: after_step
- Open ordered controls inside and outside a disabled fieldset
   - HTML capture: after_step
- Move focus to the first legend without visiting blocked controls
   - HTML capture: after_step
   - Evidence: HTML text verified by 4 expected checks
   - Expected: first_tab.semantic_target_id equals `before`
   - Expected: first_tab.callback_count equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: legend_tab.semantic_target_id equals `legend-button`
   - Expected: legend_tab.callback_count equals `2)  # oracle: pinned constant asserted by this scenario`
- Lower the allowed focus state through Draw IR and Engine2D
   - HTML capture: after_step
   - Evidence: HTML text verified by 3 expected checks
   - Expected: legend_color equals `0xFF2563EBu32`
   - Expected: blocked_positive_color equals `0xFF6B7280u32`
   - Expected: rendered.skipped_command_count equals `0)  # oracle: pinned constant asserted by this scenario`
- Continue in both directions without delivering blocked focus events
   - HTML capture: after_step
   - Evidence: HTML text verified by 4 expected checks
   - Expected: link_tab.semantic_target_id equals `fieldset-link`
   - Expected: after_tab.semantic_target_id equals `after`
   - Expected: wrapped_tab.semantic_target_id equals `before`
   - Expected: reverse_tab.semantic_target_id equals `after`


<details>
<summary>Executable SSpec</summary>

Runnable source: 131 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-004 REQ-WEB-BROWSER-007 REQ-WEB-BROWSER-008 REQ-WEB-BROWSER-021
step("Verify: should skip disabled controls and preserve the first legend exception")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Open ordered controls inside and outside a disabled fieldset")
val html = (
    "<style>body,fieldset,legend{margin:0;padding:0;border:0}" +
    "button,input,a{display:block;margin:0;padding:0;border:0;" +
    "width:56px;height:16px;background-color:#6b7280}" +
    "#legend-button[data-focused]{{background-color:#2563eb}}" +
    "#blocked-positive[data-focused]," +
    "#blocked-regular[data-focused]," +
    "#blocked-second-legend[data-focused]{" +
    "background-color:#ef4444}</style>" +
    "<button id='before' tabindex='1' " +
    "onfocus='set-attr:data-focus-fired=yes' " +
    "onblur='set-attr:data-blur-fired=yes'>Before</button>" +
    "<fieldset disabled><legend><button id='legend-button' " +
    "tabindex='2' onfocus='set-attr:data-focus-fired=yes' " +
    "onblur='set-attr:data-blur-fired=yes'>Legend</button></legend>" +
    "<button id='blocked-positive' tabindex='3' " +
    "onfocus='set-attr:data-wrong-focus=yes'>Blocked</button>" +
    "<a id='fieldset-link' href='#allowed' tabindex='4' " +
    "onfocus='set-attr:data-focus-fired=yes' " +
    "onblur='set-attr:data-blur-fired=yes'>Allowed link</a>" +
    "<legend><button id='blocked-second-legend' tabindex='5' " +
    "onfocus='set-attr:data-wrong-focus=yes'>Second</button></legend>" +
    "<input id='blocked-regular' " +
    "onfocus='set-attr:data-wrong-focus=yes'></fieldset>" +
    "<button id='after' tabindex='6' " +
    "onfocus='set-attr:data-focus-fired=yes'>After</button>"
)
var session = HostedWebContentSession.create(812, html, 64, 112)
val root = session.browser.dom_root()
val index = system_browser_dom_identity_index(session.browser)
expect(be_dom_control_is_effectively_disabled(
    root, index, system_dom_route(index, "legend-button")
)).to_be(false)
expect(be_dom_control_is_effectively_disabled(
    root, index, system_dom_route(index, "blocked-positive")
)).to_be(true)
expect(be_dom_control_is_effectively_disabled(
    root, index, system_dom_route(index, "blocked-regular")
)).to_be(true)
expect(be_dom_control_is_effectively_disabled(
    root, index, system_dom_route(index, "blocked-second-legend")
)).to_be(true)
expect(be_dom_control_is_effectively_disabled(
    root, index, system_dom_route(index, "fieldset-link")
)).to_be(false)

step("Move focus to the first legend without visiting blocked controls")
val first_tab = session.dispatch_key_with_shift(1, 9, true, false)
expect(first_tab.semantic_target_id).to_equal("before")
expect(first_tab.callback_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
val legend_tab = session.dispatch_key_with_shift(2, 9, true, false)
expect(legend_tab.semantic_target_id).to_equal("legend-button")
expect(legend_tab.callback_count).to_equal(2)  # oracle: pinned constant asserted by this scenario
val focused_root = session.browser.dom_root()
val focused_index = system_browser_dom_identity_index(session.browser)
expect(system_dom_focused_route(
    focused_root, focused_index
).node_id).to_equal(system_dom_route(
    focused_index, "legend-button"
).node_id)
expect(fieldset_focus_has_attr(
    session, "before", "data-blur-fired"
)).to_be(true)
expect(fieldset_focus_has_attr(
    session, "legend-button", "data-focus-fired"
)).to_be(true)
expect(fieldset_focus_has_attr(
    session, "blocked-positive", "data-wrong-focus"
)).to_be(false)

step("Lower the allowed focus state through Draw IR and Engine2D")
val composition = WebRenderBackend.create(
    "pure_simple", 64, 112
).render_html_to_draw_ir(session.browser.render_html_document())
var legend_color = 0u32
var blocked_positive_color = 0u32
for batch in composition.batches:
    for command in batch.commands:
        if command.component_id == "legend-button":
            legend_color = command.color
        elif command.component_id == "blocked-positive":
            blocked_positive_color = command.color
expect(legend_color).to_equal(0xFF2563EBu32)
expect(blocked_positive_color).to_equal(0xFF6B7280u32)
val engine = Engine2dCompositorBackend.create_named(
    64, 112, "software"
)
val rendered = engine.render_draw_ir_composition_resources(
    composition, session.browser.image_resources
)
expect(rendered.skipped_command_count).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(fieldset_focus_color_count(
    rendered.pixels, 0xFF2563EBu32
)).to_be_greater_than(0)
expect(fieldset_focus_color_count(
    rendered.pixels, 0xFFEF4444u32
)).to_equal(0)  # oracle: pinned constant asserted by this scenario
engine.shutdown()

step("Continue in both directions without delivering blocked focus events")
val link_tab = session.dispatch_key_with_shift(3, 9, true, false)
expect(link_tab.semantic_target_id).to_equal("fieldset-link")
val after_tab = session.dispatch_key_with_shift(4, 9, true, false)
expect(after_tab.semantic_target_id).to_equal("after")
val wrapped_tab = session.dispatch_key_with_shift(5, 9, true, false)
expect(wrapped_tab.semantic_target_id).to_equal("before")
val reverse_tab = session.dispatch_key_with_shift(6, 9, true, true)
expect(reverse_tab.semantic_target_id).to_equal("after")
expect(fieldset_focus_has_attr(
    session, "blocked-positive", "data-wrong-focus"
)).to_be(false)
expect(fieldset_focus_has_attr(
    session, "blocked-regular", "data-wrong-focus"
)).to_be(false)
expect(fieldset_focus_has_attr(
    session, "blocked-second-legend", "data-wrong-focus"
)).to_be(false)
expect(fieldset_focus_has_attr(
    session, "blocked-positive", "data-focused"
)).to_be(false)
expect(fieldset_focus_has_attr(
    session, "blocked-regular", "data-focused"
)).to_be(false)
expect(fieldset_focus_has_attr(
    session, "blocked-second-legend", "data-focused"
)).to_be(false)
session.close()
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

- Canonical SPipe generation for source `fc62904b5adac0918008ac19d420ec66ed0e1437e06b8ec6281f03774ccd35d5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fc62904b5adac0918008ac19d420ec66ed0e1437e06b8ec6281f03774ccd35d5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fc62904b5adac0918008ac19d420ec66ed0e1437e06b8ec6281f03774ccd35d5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/browser/feature/browser_disabled_fieldset_sequential_focus_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/browser_disabled_fieldset_sequential_focus_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/browser/feature/browser_disabled_fieldset_sequential_focus_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/browser/feature/browser_disabled_fieldset_sequential_focus_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/browser_disabled_fieldset_sequential_focus_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser/feature/browser_disabled_fieldset_sequential_focus_spec.spl:63:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should skip disabled controls and preserve the first legend exception' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
