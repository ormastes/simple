# Hosted negative-tabindex pointer focus

> Verifies the browser negative tabindex pointer focus behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hosted negative-tabindex pointer focus

Verifies the browser negative tabindex pointer focus behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/browser/feature/browser_negative_tabindex_pointer_focus_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the browser negative tabindex pointer focus behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Hosted negative-tabindex pointer focus

#### should pointer-focus a negative tabindex control and skip it on Tab

**Manual warnings:**
- invalid capture metadata value: draw_ir (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Verify: should pointer-focus a negative tabindex control and skip it on Tab
   - HTML capture: after_step
- Open a pointer-focusable control outside sequential Tab order
   - HTML capture: after_step
- Press the control and observe focus before pointer release
   - HTML capture: after_step
   - Evidence: HTML text verified by 2 expected checks
   - Expected: down.semantic_target_id equals `pointer-only`
   - Expected: session.browser.current_title equals `js-focus`
- Lower focused state through Draw IR and Engine2D
   - HTML capture: after_step
   - Evidence: HTML text verified by 2 expected checks
   - Expected: focus_color equals `0xFF2563EBu32`
   - Expected: rendered.skipped_command_count equals `0)  # oracle: pinned constant asserted by this scenario`
- Release the pointer and move sequential focus with Tab
   - HTML capture: after_step
   - Evidence: HTML text verified by 5 expected checks
   - Expected: up.semantic_target_id equals `pointer-only`
   - Expected: tab.semantic_target_id equals `next`
   - Expected: reverse_down.semantic_target_id equals `pointer-only`
   - Expected: reverse_up.semantic_target_id equals `pointer-only`
   - Expected: reverse_tab.semantic_target_id equals `previous`


<details>
<summary>Executable SSpec</summary>

Runnable source: 90 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-005 REQ-WEB-BROWSER-007 REQ-WEB-BROWSER-008
step("Verify: should pointer-focus a negative tabindex control and skip it on Tab")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Open a pointer-focusable control outside sequential Tab order")
val html = (
    "<style>body{{margin:0}}input,button{display:block;margin:0;" +
    "padding:0;border:0;width:48px;height:20px;" +
    "background-color:#ef4444}" +
    "#pointer-only[data-focused]{{background-color:#2563eb}}</style>" +
    "<button id='previous'>Previous</button>" +
    "<input id='pointer-only' tabindex='-1' " +
    "onfocus='set-attr:data-simple-focus=yes'>" +
    "<button id='next'>Next</button><script>" +
    "document.getElementById('pointer-only').addEventListener(" +
    "'focus',function(event){document.title='js-'+event.type;});" +
    "</script>"
)
var session = HostedWebContentSession.create(811, html, 64, 48)

step("Press the control and observe focus before pointer release")
val down = session.dispatch_pointer_at(1, 4, 24, true)
expect(down.semantic_target_id).to_equal("pointer-only")
val down_root = session.browser.dom_root()
val down_index = system_browser_dom_identity_index(session.browser)
expect(system_dom_focused_route(
    down_root, down_index
).node_id).to_equal(system_dom_route(
    down_index, "pointer-only"
).node_id)
expect(session.current_body_html()).to_contain(
    "data-focused=\"true\""
)
expect(session.current_body_html()).to_contain(
    "data-simple-focus=\"yes\""
)
expect(session.browser.current_title).to_equal("js-focus")

step("Lower focused state through Draw IR and Engine2D")
val composition = WebRenderBackend.create(
    "pure_simple", 64, 48
).render_html_to_draw_ir(session.browser.render_html_document())
var focus_command_found = false
var focus_color = 0u32
for batch in composition.batches:
    for command in batch.commands:
        if command.component_id == "pointer-only":
            focus_command_found = true
            focus_color = command.color
expect(focus_command_found).to_be(true)
expect(focus_color).to_equal(0xFF2563EBu32)

val engine = Engine2dCompositorBackend.create_named(
    64, 48, "software"
)
val rendered = engine.render_draw_ir_composition_resources(
    composition, session.browser.image_resources
)
expect(rendered.skipped_command_count).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(negative_tabindex_color_count(
    rendered.pixels, 0xFF2563EBu32
)).to_be_greater_than(0)
engine.shutdown()

step("Release the pointer and move sequential focus with Tab")
val up = session.dispatch_pointer_at(2, 4, 24, false)
expect(up.semantic_target_id).to_equal("pointer-only")
val tab = session.dispatch_key_with_shift(3, 9, true, false)
expect(tab.semantic_target_id).to_equal("next")
val tab_root = session.browser.dom_root()
val tab_index = system_browser_dom_identity_index(session.browser)
expect(system_dom_focused_route(
    tab_root, tab_index
).node_id).to_equal(system_dom_route(tab_index, "next").node_id)

val reverse_down = session.dispatch_pointer_at(4, 4, 24, true)
expect(reverse_down.semantic_target_id).to_equal("pointer-only")
val reverse_up = session.dispatch_pointer_at(5, 4, 24, false)
expect(reverse_up.semantic_target_id).to_equal("pointer-only")
val reverse_tab = session.dispatch_key_with_shift(
    6, 9, true, true
)
expect(reverse_tab.semantic_target_id).to_equal("previous")
val reverse_root = session.browser.dom_root()
val reverse_index = system_browser_dom_identity_index(session.browser)
expect(system_dom_focused_route(
    reverse_root, reverse_index
).node_id).to_equal(system_dom_route(
    reverse_index, "previous"
).node_id)
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

- Canonical SPipe generation for source `6dbc831d2c18088b679011ff7bd233eaa419cabe52b449e44e2c1de59203d217`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6dbc831d2c18088b679011ff7bd233eaa419cabe52b449e44e2c1de59203d217`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6dbc831d2c18088b679011ff7bd233eaa419cabe52b449e44e2c1de59203d217`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/browser/feature/browser_negative_tabindex_pointer_focus_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/browser_negative_tabindex_pointer_focus_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/browser/feature/browser_negative_tabindex_pointer_focus_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/browser/feature/browser_negative_tabindex_pointer_focus_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/browser_negative_tabindex_pointer_focus_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser/feature/browser_negative_tabindex_pointer_focus_spec.spl:47:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should pointer-focus a negative tabindex control and skip it on Tab' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
