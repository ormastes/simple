# Hosted negative-tabindex pointer focus

> A negative tabindex keeps a control pointer-focusable while excluding it from

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hosted negative-tabindex pointer focus

A negative tabindex keeps a control pointer-focusable while excluding it from

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/browser/feature/browser_negative_tabindex_pointer_focus_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

A negative tabindex keeps a control pointer-focusable while excluding it from
sequential Tab navigation. The scenario follows the production hosted pointer,
DOM event, Draw IR, and Engine2D routes.

## Scenarios

### Hosted negative-tabindex pointer focus

#### should pointer-focus a negative tabindex control and skip it on Tab

**Manual warnings:**
- invalid capture metadata value: draw_ir (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- should pointer-focus a negative tabindex control and skip it on Tab
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
   - Expected: rendered.skipped_command_count equals `0`
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

Runnable source: 89 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should pointer-focus a negative tabindex control and skip it on Tab")
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
expect(rendered.skipped_command_count).to_equal(0)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-WEB-BROWSER-005`
- `REQ-WEB-BROWSER-007`
- `REQ-WEB-BROWSER-008`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9fc3d162f3fcb220180a2e3e758d518bca1bdf974ce6eb041ccb88a6d8485465`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9fc3d162f3fcb220180a2e3e758d518bca1bdf974ce6eb041ccb88a6d8485465`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9fc3d162f3fcb220180a2e3e758d518bca1bdf974ce6eb041ccb88a6d8485465`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/browser/feature/browser_negative_tabindex_pointer_focus_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/browser_negative_tabindex_pointer_focus_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=95 oracle=90
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/03_system/app/browser/feature/browser_negative_tabindex_pointer_focus_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/browser_negative_tabindex_pointer_focus_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser/feature/browser_negative_tabindex_pointer_focus_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/browser/feature/browser_negative_tabindex_pointer_focus_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/app/browser/feature/browser_negative_tabindex_pointer_focus_spec.spl:37:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should pointer-focus a negative tabindex control and skip it on Tab' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/browser/feature/browser_negative_tabindex_pointer_focus_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should pointer-focus a negative tabindex control and skip it on Tab' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
