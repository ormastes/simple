# Hosted Browser InputEvent Payload

> Verifies the browser input event payload behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hosted Browser InputEvent Payload

Verifies the browser input event payload behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/browser/feature/browser_input_event_payload_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the browser input event payload behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Hosted browser InputEvent payload

#### should preserve UTF-8 insertion and deletion payloads through pixels

- Verify: should preserve UTF-8 insertion and deletion payloads through pixels
   - Artifact capture: after_step
- Open and focus the hosted text control
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: session.last_target_id equals `q`
- Commit one UTF-8 insertion with exact InputEvent data
   - Artifact capture: after_step
   - Evidence: artifact verified by 3 expected checks
   - Expected: inserted.reason equals ``
   - Expected: session.browser.text_selection_anchor_byte equals `5)  # oracle: pinned constant asserted by this scenario`
   - Expected: session.browser.text_selection_focus_byte equals `5)  # oracle: pinned constant asserted by this scenario`
- Delete backward and forward before committing change
   - Artifact capture: after_step
   - Evidence: artifact verified by 6 expected checks
   - Expected: backspace.reason equals ``
   - Expected: deleted.reason equals ``
   - Expected: canceled_edit.semantic_target_id equals `canceled`
   - Expected: canceled.browser.current_title equals `canceled-before>`
   - Expected: canceled.browser.text_selection_anchor_byte equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: canceled.browser.text_selection_focus_byte equals `3)  # oracle: pinned constant asserted by this scenario`
- Lower the listener mutation through Draw IR and Engine2D
   - Artifact capture: after_step
   - Evidence: artifact verified by 2 expected checks
   - Expected: probe_color equals `0xFF2563EBu32`
   - Expected: rendered.skipped_command_count equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 151 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-004 REQ-WEB-BROWSER-008 REQ-WEB-BROWSER-021
step("Verify: should preserve UTF-8 insertion and deletion payloads through pixels")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Open and focus the hosted text control")
val html = (
    "<style>body{{margin:0}}input{display:block;width:48px;height:20px}" +
    "#probe{width:32px;height:24px;background-color:#ef4444}" +
    "#probe.ok{{background-color:#2563eb}}</style>" +
    "<input id='q' value='A' onchange=\"" +
    "document.title=document.title+'change>'\">" +
    "<div id='probe'></div><script>" +
    "var q=document.getElementById('q');var redirected=false;" +
    "var beforeBackwardNull=false;var inputBackwardNull=false;" +
    "var beforeForwardNull=false;var inputForwardNull=false;" +
    "var genericEventMissing=false;" +
    "q.addEventListener('keydown',function(event){" +
    "genericEventMissing=typeof event.data==='undefined'&&" +
    "typeof event.inputType==='undefined'&&" +
    "typeof event.isComposing==='undefined';});" +
    "q.addEventListener('beforeinput',function(event){" +
    "if(event.inputType==='deleteContentBackward'){" +
    "beforeBackwardNull=event.data===null;}" +
    "if(event.inputType==='deleteContentForward'){" +
    "beforeForwardNull=event.data===null;}" +
    "if(event.inputType==='insertText'&&!redirected){" +
    "this.value='éY';this.selectionStart=2;" +
    "this.selectionEnd=3;redirected=true;}" +
    "document.title=document.title+'before:'+event.data+'|'+" +
    "event.inputType+'|'+event.isComposing+'>';});" +
    "q.addEventListener('input',function(event){" +
    "if(event.inputType==='deleteContentBackward'){" +
    "inputBackwardNull=event.data===null;}" +
    "if(event.inputType==='deleteContentForward'){" +
    "inputForwardNull=event.data===null;}" +
    "document.title=document.title+'input:'+event.data+'|'+" +
    "event.inputType+'|'+event.isComposing+'>';" +
    "if(event.data==='한'&&event.inputType==='insertText'&&" +
    "!event.isComposing){" +
    "document.getElementById('probe').className='ok';}});" +
    "</script>"
)
var session = HostedWebContentSession.create(23, html, 80, 64)
val before_pixels = session.render_to_pixels()
expect(input_event_color_count(
    before_pixels, 0xFFEF4444u32
)).to_be_greater_than(0)
val _ = session.dispatch_pointer_at(1, 4, 4, true)
val _ = session.dispatch_pointer_at(2, 4, 4, false)
expect(session.last_target_id).to_equal("q")

step("Commit one UTF-8 insertion with exact InputEvent data")
val inserted = session.dispatch_text(3, "한")
expect(inserted.reason).to_equal("")
expect(session.browser.current_title).to_equal(
    "before:한|insertText|false>input:한|insertText|false>"
)
expect(session.current_body_html()).to_contain("value=\"é한\"")
expect(session.browser.text_selection_anchor_byte).to_equal(5)  # oracle: pinned constant asserted by this scenario
expect(session.browser.text_selection_focus_byte).to_equal(5)  # oracle: pinned constant asserted by this scenario

step("Delete backward and forward before committing change")
val backspace = session.dispatch_key(4, 8, true)
expect(backspace.reason).to_equal("")
expect(session.browser.current_title).to_end_with(
    "before:null|deleteContentBackward|false>" +
    "input:null|deleteContentBackward|false>"
)
expect(session.current_body_html()).to_contain("value=\"é\"")
expect(session.browser.set_dom_text_selection("q", 0, 0)).to_be(true)
val deleted = session.dispatch_key(5, 46, true)
expect(deleted.reason).to_equal("")
expect(session.browser.current_title).to_end_with(
    "before:null|deleteContentForward|false>" +
    "input:null|deleteContentForward|false>"
)
expect(session.current_body_html()).to_contain("value=\"\"")
expect(session.browser.eval_script(
    "document.title=document.title+'sentinels:'+" +
    "beforeBackwardNull+'|'+inputBackwardNull+'|'+" +
    "beforeForwardNull+'|'+inputForwardNull+'|'+" +
    "genericEventMissing+'>'"
).is_ok()).to_be(true)
expect(session.browser.current_title).to_end_with(
    "sentinels:true|true|true|true|true>"
)
expect(session.browser.blur_dom_text_input("q").is_ok()).to_be(true)
expect(session.browser.current_title).to_equal(
    "before:한|insertText|false>input:한|insertText|false>" +
    "before:null|deleteContentBackward|false>" +
    "input:null|deleteContentBackward|false>" +
    "before:null|deleteContentForward|false>" +
    "input:null|deleteContentForward|false>" +
    "sentinels:true|true|true|true|true>change>"
)

val canceled_html = (
    "<input id='canceled' value='A'><script>" +
    "var canceled=document.getElementById('canceled');" +
    "canceled.addEventListener('beforeinput',function(event){" +
    "this.value='éZ';this.selectionStart=2;this.selectionEnd=3;" +
    "document.title='canceled-before>';event.preventDefault();});" +
    "canceled.addEventListener('input',function(event){" +
    "document.title=document.title+'wrong-input>';});</script>"
)
var canceled = HostedWebContentSession.create(
    24, canceled_html, 80, 40
)
val _ = canceled.dispatch_pointer_at(6, 4, 4, true)
val _ = canceled.dispatch_pointer_at(7, 4, 4, false)
val canceled_edit = canceled.dispatch_text(8, "한")
expect(canceled_edit.semantic_target_id).to_equal("canceled")
expect(canceled.browser.current_title).to_equal("canceled-before>")
expect(canceled.current_body_html()).to_contain("value=\"éZ\"")
expect(canceled.current_body_html().contains(
    "data-input-dirty"
)).to_be(false)
expect(canceled.browser.text_selection_anchor_byte).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(canceled.browser.text_selection_focus_byte).to_equal(3)  # oracle: pinned constant asserted by this scenario
canceled.close()

step("Lower the listener mutation through Draw IR and Engine2D")
val document = session.browser.render_html_document()
val composition = WebRenderBackend.create(
    "pure_simple", 80, 64
).render_html_to_draw_ir(document)
var probe_found = false
var probe_color = 0u32
for batch in composition.batches:
    for command in batch.commands:
        if command.component_id == "probe":
            probe_found = true
            probe_color = command.color
expect(probe_found).to_be(true)
expect(probe_color).to_equal(0xFF2563EBu32)

val engine = Engine2dCompositorBackend.create_named(
    80, 64, "software"
)
val rendered = engine.render_draw_ir_composition_resources(
    composition, session.browser.image_resources
)
expect(rendered.skipped_command_count).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(rendered.rendered_command_count).to_be_greater_than(0)
expect(input_event_color_count(
    rendered.pixels, 0xFF2563EBu32
)).to_be_greater_than(0)
expect(input_event_color_count(
    rendered.pixels, 0xFFEF4444u32
)).to_equal(0)  # oracle: pinned constant asserted by this scenario
engine.shutdown()
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

- Canonical SPipe generation for source `cb61837727c782aea34cf8dc66454c6f06571dc5b1c999531cd614a67387f7cd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cb61837727c782aea34cf8dc66454c6f06571dc5b1c999531cd614a67387f7cd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cb61837727c782aea34cf8dc66454c6f06571dc5b1c999531cd614a67387f7cd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/browser/feature/browser_input_event_payload_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/browser_input_event_payload_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/browser/feature/browser_input_event_payload_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/browser/feature/browser_input_event_payload_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/browser_input_event_payload_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser/feature/browser_input_event_payload_spec.spl:43:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve UTF-8 insertion and deletion payloads through pixels' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
