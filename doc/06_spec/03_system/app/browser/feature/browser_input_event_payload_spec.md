# Hosted Browser InputEvent Payload

> This scenario proves that committed UTF-8 text and deletion keys keep their

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hosted Browser InputEvent Payload

This scenario proves that committed UTF-8 text and deletion keys keep their

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/browser/feature/browser_input_event_payload_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

This scenario proves that committed UTF-8 text and deletion keys keep their
InputEvent payload while crossing the hosted session, live DOM, JavaScript
listener, Draw IR, and Engine2D boundaries.

## Scenarios

### Hosted browser InputEvent payload

#### should preserve UTF-8 insertion and deletion payloads through pixels

- should preserve UTF-8 insertion and deletion payloads through pixels
   - Artifact capture: after_step
- Open and focus the hosted text control
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: session.last_target_id equals `q`
- Commit one UTF-8 insertion with exact InputEvent data
   - Artifact capture: after_step
   - Evidence: artifact verified by 3 expected checks
   - Expected: inserted.reason equals ``
   - Expected: session.browser.text_selection_anchor_byte equals `5`
   - Expected: session.browser.text_selection_focus_byte equals `5`
- Delete backward and forward before committing change
   - Artifact capture: after_step
   - Evidence: artifact verified by 6 expected checks
   - Expected: backspace.reason equals ``
   - Expected: deleted.reason equals ``
   - Expected: canceled_edit.semantic_target_id equals `canceled`
   - Expected: canceled.browser.current_title equals `canceled-before>`
   - Expected: canceled.browser.text_selection_anchor_byte equals `2`
   - Expected: canceled.browser.text_selection_focus_byte equals `3`
- Lower the listener mutation through Draw IR and Engine2D
   - Artifact capture: after_step
   - Evidence: artifact verified by 2 expected checks
   - Expected: probe_color equals `0xFF2563EBu32`
   - Expected: rendered.skipped_command_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 150 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve UTF-8 insertion and deletion payloads through pixels")
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
expect(session.browser.text_selection_anchor_byte).to_equal(5)
expect(session.browser.text_selection_focus_byte).to_equal(5)

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
expect(canceled.browser.text_selection_anchor_byte).to_equal(2)
expect(canceled.browser.text_selection_focus_byte).to_equal(3)
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
expect(rendered.skipped_command_count).to_equal(0)
expect(rendered.rendered_command_count).to_be_greater_than(0)
expect(input_event_color_count(
    rendered.pixels, 0xFF2563EBu32
)).to_be_greater_than(0)
expect(input_event_color_count(
    rendered.pixels, 0xFFEF4444u32
)).to_equal(0)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-WEB-BROWSER-004`
- `REQ-WEB-BROWSER-008`
- `REQ-WEB-BROWSER-021`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `48b1017f085c50fb256ee2536259fd288357f14633b82e64ef769cf4544d8daf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `48b1017f085c50fb256ee2536259fd288357f14633b82e64ef769cf4544d8daf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `48b1017f085c50fb256ee2536259fd288357f14633b82e64ef769cf4544d8daf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/browser/feature/browser_input_event_payload_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/browser_input_event_payload_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=95 oracle=70
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/03_system/app/browser/feature/browser_input_event_payload_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/browser_input_event_payload_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser/feature/browser_input_event_payload_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/browser/feature/browser_input_event_payload_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/app/browser/feature/browser_input_event_payload_spec.spl:33:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve UTF-8 insertion and deletion payloads through pixels' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/browser/feature/browser_input_event_payload_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve UTF-8 insertion and deletion payloads through pixels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
