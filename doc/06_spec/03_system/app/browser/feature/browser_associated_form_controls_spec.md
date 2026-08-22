# browser_associated_form_controls_spec

> Verifies the browser associated form controls behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# browser_associated_form_controls_spec

Verifies the browser associated form controls behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/browser/feature/browser_associated_form_controls_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the browser associated form controls behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Evidence

Display policy: `embed_tui`

| Category | Count |
|----------|------:|
| Screenshots | 2 |

### Screenshots

| Item | Kind | Path |
|------|------|------|
| `pixel oracle is retained in-memory` | Screenshot | `pixel oracle is retained in-memory` |
| `the visible control is` | Screenshot | `the visible control is` |

## Scenarios

### BrowserSession associated form controls

#### should submit an externally associated control after its visible click

- Verify: should submit an externally associated control after its visible click
- Render the browser form and locate its visible submit button
   - Expected: buttons.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: pixels_before.len() equals `256)  # oracle: pinned constant asserted by this scenario`
- Release the submit button through the DOM UI action route
- Observe click state, serialized POST event, and unchanged page pixels
   - Expected: activated.ok is true
   - Expected: session.current_title equals `Sending`
   - Expected: request.method equals `POST`
   - Expected: request.url equals `https://example.com/save`
   - Expected: request.body equals `name=Ada&role=editor&intent=publish`
   - Expected: request.body does not contain `leak=blocked`
   - Expected: request.content_type equals `application/x-www-form-urlencoded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-007 REQ-WEB-BROWSER-008 REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-021
step("Verify: should submit an externally associated control after its visible click")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Render the browser form and locate its visible submit button")
var session = BrowserSession.new()
expect(session.open_html(
    "https://example.com/profile",
    "<html><body><form id='profile' action='/save' method='post'><input name='name' value='Ada'></form><input form='profile' name='role' value='editor'><input form='other' name='leak' value='blocked'><form id='other'></form><button form='profile' name='intent' value='publish' onclick=\"document.title='Sending'\">Send</button></body></html>"
).is_ok()).to_equal(true)
val pixels_before = session.render_to_pixels(16, 16).pixels
val buttons = ui_access_find_nodes(
    session.ui_access_snapshot(), "browser:session", "button", "Send", 1
)
expect(buttons.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(pixels_before.len()).to_equal(256)  # oracle: pinned constant asserted by this scenario

step("Release the submit button through the DOM UI action route")
val activated = session.ui_access_act(WinTextActionRequest(
    target_id: buttons[0].canonical_id, action: "click",
    text_value: "", x: 0, y: 0
))

step("Observe click state, serialized POST event, and unchanged page pixels")
expect(activated.ok).to_equal(true)
expect(session.current_title).to_equal("Sending")
if val request = session.take_pending_request():
    expect(request.method).to_equal("POST")
    expect(request.url).to_equal("https://example.com/save")
    expect(request.body).to_equal("name=Ada&role=editor&intent=publish")
    expect(request.body.contains("leak=blocked")).to_equal(false)
    expect(request.content_type).to_equal("application/x-www-form-urlencoded")
else:
    fail("missing form request")
expect(_same_pixels(
    session.render_to_pixels(16, 16).pixels, pixels_before
)).to_equal(true)
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

- Canonical SPipe generation for source `e652526ac66ef7e9a2fb461925ff768bef6a187dce43a25f87f9249452ec752f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e652526ac66ef7e9a2fb461925ff768bef6a187dce43a25f87f9249452ec752f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e652526ac66ef7e9a2fb461925ff768bef6a187dce43a25f87f9249452ec752f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/browser/feature/browser_associated_form_controls_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/browser_associated_form_controls_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/browser/feature/browser_associated_form_controls_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/browser/feature/browser_associated_form_controls_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/browser_associated_form_controls_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser/feature/browser_associated_form_controls_spec.spl:51:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should submit an externally associated control after its visible click' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
