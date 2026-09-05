# Hosted disabled-fieldset sequential focus

> Sequential Tab navigation must skip form controls disabled by a fieldset while

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hosted disabled-fieldset sequential focus

Sequential Tab navigation must skip form controls disabled by a fieldset while

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/browser/feature/browser_disabled_fieldset_sequential_focus_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Sequential Tab navigation must skip form controls disabled by a fieldset while
keeping the first legend subtree and non-form focusable descendants eligible.
The scenario follows the production hosted keyboard, DOM event, Draw IR, and
Engine2D routes.

## Scenarios

### Hosted disabled-fieldset sequential focus

#### should skip disabled controls and preserve the first legend exception

**Manual warnings:**
- invalid capture metadata value: draw_ir (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- should skip disabled controls and preserve the first legend exception
   - HTML capture: after_step
- Open ordered controls inside and outside a disabled fieldset
   - HTML capture: after_step
- Move focus to the first legend without visiting blocked controls
   - HTML capture: after_step
   - Evidence: HTML text verified by 4 expected checks
   - Expected: first_tab.semantic_target_id equals `before`
   - Expected: first_tab.callback_count equals `1`
   - Expected: legend_tab.semantic_target_id equals `legend-button`
   - Expected: legend_tab.callback_count equals `2`
- Lower the allowed focus state through Draw IR and Engine2D
   - HTML capture: after_step
   - Evidence: HTML text verified by 3 expected checks
   - Expected: legend_color equals `0xFF2563EBu32`
   - Expected: blocked_positive_color equals `0xFF6B7280u32`
   - Expected: rendered.skipped_command_count equals `0`
- Continue in both directions without delivering blocked focus events
   - HTML capture: after_step
   - Evidence: HTML text verified by 4 expected checks
   - Expected: link_tab.semantic_target_id equals `fieldset-link`
   - Expected: after_tab.semantic_target_id equals `after`
   - Expected: wrapped_tab.semantic_target_id equals `before`
   - Expected: reverse_tab.semantic_target_id equals `after`


<details>
<summary>Executable SSpec</summary>

Runnable source: 130 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should skip disabled controls and preserve the first legend exception")
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
expect(first_tab.callback_count).to_equal(1)
val legend_tab = session.dispatch_key_with_shift(2, 9, true, false)
expect(legend_tab.semantic_target_id).to_equal("legend-button")
expect(legend_tab.callback_count).to_equal(2)
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
expect(rendered.skipped_command_count).to_equal(0)
expect(fieldset_focus_color_count(
    rendered.pixels, 0xFF2563EBu32
)).to_be_greater_than(0)
expect(fieldset_focus_color_count(
    rendered.pixels, 0xFFEF4444u32
)).to_equal(0)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-WEB-BROWSER-004`
- `REQ-WEB-BROWSER-007`
- `REQ-WEB-BROWSER-008`
- `REQ-WEB-BROWSER-021`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b96d32a6cc554afc2107b7539d497f29b8c063714049e28ab044373b5f9d2b2b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b96d32a6cc554afc2107b7539d497f29b8c063714049e28ab044373b5f9d2b2b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b96d32a6cc554afc2107b7539d497f29b8c063714049e28ab044373b5f9d2b2b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/browser/feature/browser_disabled_fieldset_sequential_focus_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/browser_disabled_fieldset_sequential_focus_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=95 oracle=70
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/03_system/app/browser/feature/browser_disabled_fieldset_sequential_focus_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/browser_disabled_fieldset_sequential_focus_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser/feature/browser_disabled_fieldset_sequential_focus_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/browser/feature/browser_disabled_fieldset_sequential_focus_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 4 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/app/browser/feature/browser_disabled_fieldset_sequential_focus_spec.spl:53:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should skip disabled controls and preserve the first legend exception' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/browser/feature/browser_disabled_fieldset_sequential_focus_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should skip disabled controls and preserve the first legend exception' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
