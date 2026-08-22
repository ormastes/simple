# browser_address_selection_backspace_spec

> Verifies the browser address selection backspace behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# browser_address_selection_backspace_spec

Verifies the browser address selection backspace behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | REQ-WEB-BROWSER-007, REQ-WEB-BROWSER-008 |
| Source | `test/03_system/app/browser/feature/browser_address_selection_backspace_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the browser address selection backspace behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Browser address selection Backspace

#### should clear the selected address without changing the committed page

- Verify: should clear the selected address without changing the committed page
- Commit pages and capture their navigation and rendered state
- Focus each address bar and select its complete value
   - Expected: hosted.chrome_focus equals `address`
   - Expected: worker.chrome_focus equals `address`
- Press Backspace once through every executable chrome route
   - Expected: hosted_backspace.callback_count equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: registry_backspace.callback_count equals `1)  # oracle: pinned constant asserted by this scenario`
- Keep focus while clearing the selection and preserving the page
   - Expected: hosted.browser.address_draft equals ``
   - Expected: hosted.address_text() equals ``
   - Expected: hosted.chrome_focus equals `address`
   - Expected: hosted.browser.current_url equals `hosted_url`
   - Expected: hosted.browser.history.len() equals `hosted_history`
   - Expected: hosted.browser.current_index equals `hosted_index`
   - Expected: hosted.browser.current_body_html equals `hosted_body`
   - Expected: worker.browser.address_draft equals ``
   - Expected: worker.chrome_focus equals `address`
   - Expected: worker.browser.current_url equals `worker_url`
   - Expected: worker.browser.history.len() equals `worker_history`
   - Expected: worker.browser.current_index equals `worker_index`
   - Expected: worker.browser.current_body_html equals `worker_body`
   - Expected: registry.address_text(62) equals ``
   - Expected: registry.document_url(62) equals `registry_url`
   - Expected: hosted_second.callback_count equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: hosted.address_text() equals ``
   - Expected: worker.browser.address_draft equals ``
   - Expected: registry_second.callback_count equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: registry.address_text(62) equals ``
   - Expected: hosted_typed.callback_count equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: hosted.address_text() equals `x`
   - Expected: worker.browser.address_draft equals `x`
   - Expected: registry_typed.callback_count equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: registry.address_text(62) equals `x`
   - Expected: hosted.browser.current_url equals `hosted_url`
   - Expected: worker.browser.current_url equals `worker_url`
   - Expected: registry.document_url(62) equals `registry_url`
   - Expected: reason equals `address-invalid-utf8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 169 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-007 REQ-WEB-BROWSER-008
step("Verify: should clear the selected address without changing the committed page")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Commit pages and capture their navigation and rendered state")
var hosted = HostedWebContentSession.create(
    61, "<p>start</p>", 32, 16
)
expect(hosted.browser.open_html(
    "https://committed.test/page",
    "<html><body><p>committed</p></body></html>"
).is_ok()).to_be(true)
val hosted_url = hosted.browser.current_url
val hosted_history = hosted.browser.history.len()
val hosted_index = hosted.browser.current_index
val hosted_body = hosted.browser.current_body_html
val hosted_pixels = hosted.browser.render_to_pixels(32, 16).pixels

var worker = HostedBrowserRendererWorkerSession.create(32, 16)
expect(worker.handle(BrowserRendererMessage(
    kind: "init", generation: 7, request_id: 1,
    payload: "<html><body><p>worker</p></body></html>"
)).ok).to_be(true)
val worker_url = worker.browser.current_url
val worker_history = worker.browser.history.len()
val worker_index = worker.browser.current_index
val worker_body = worker.browser.current_body_html
val worker_pixels = worker.browser.render_to_pixels(32, 16).pixels

var registry = HostedBrowserRendererRegistry.create(
    "/bin/false", "https://home.test/"
)
val _ = registry.ensure(
    62, "<html><body><p>registry</p></body></html>",
    32, 16, 0, 100000
)
val registry_url = registry.document_url(62)
val registry_operation = registry.entries[0].renderer.pending_operation
val registry_pixels = registry.entries[0].pending_frame.pixels

step("Focus each address bar and select its complete value")
val _ = hosted.dispatch_chrome_pointer(1, "address", true)
val _ = hosted.dispatch_chrome_pointer(2, "address", false)
expect(hosted.chrome_focus).to_equal("address")
expect(hosted.address_replace_on_text).to_be(true)

expect(worker.handle(BrowserRendererMessage(
    kind: "chrome", generation: 7, request_id: 2,
    payload: "C1\t1\t1\t7\naddress"
)).ok).to_be(true)
expect(worker.handle(BrowserRendererMessage(
    kind: "chrome", generation: 7, request_id: 3,
    payload: "C1\t2\t0\t7\naddress"
)).ok).to_be(true)
expect(worker.chrome_focus).to_equal("address")
expect(worker.address_replace_on_text).to_be(true)

val _ = registry.dispatch_chrome_pointer(
    3, 62, "address", true
)
val _ = registry.dispatch_chrome_pointer(
    4, 62, "address", false
)
expect(registry.entries[0].address_editing).to_be(true)
expect(registry.entries[0].address_replace_on_text).to_be(true)

step("Press Backspace once through every executable chrome route")
val hosted_backspace = hosted.dispatch_key(5, 8, true)
val worker_backspace = worker.handle(BrowserRendererMessage(
    kind: "key", generation: 7, request_id: 4,
    payload: "K1\t1\t8\t1"
))
val registry_backspace = registry.dispatch_key_with_shift(
    6, 62, 8, true, false
)
expect(hosted_backspace.callback_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(worker_backspace.ok).to_be(true)
expect(registry_backspace.callback_count).to_equal(1)  # oracle: pinned constant asserted by this scenario

step("Keep focus while clearing the selection and preserving the page")
expect(hosted.browser.address_draft).to_equal("")
expect(hosted.address_text()).to_equal("")
expect(hosted.chrome_focus).to_equal("address")
expect(hosted.address_replace_on_text).to_be(false)
expect(hosted.browser.current_url).to_equal(hosted_url)
expect(hosted.browser.history.len()).to_equal(hosted_history)
expect(hosted.browser.current_index).to_equal(hosted_index)
expect(hosted.browser.current_body_html).to_equal(hosted_body)
expect(_pixels_equal(
    hosted.browser.render_to_pixels(32, 16).pixels, hosted_pixels
)).to_be(true)

expect(worker.browser.address_draft).to_equal("")
expect(worker.chrome_focus).to_equal("address")
expect(worker.address_replace_on_text).to_be(false)
expect(worker.browser.current_url).to_equal(worker_url)
expect(worker.browser.history.len()).to_equal(worker_history)
expect(worker.browser.current_index).to_equal(worker_index)
expect(worker.browser.current_body_html).to_equal(worker_body)
expect(_pixels_equal(
    worker.browser.render_to_pixels(32, 16).pixels, worker_pixels
)).to_be(true)

expect(registry.address_text(62)).to_equal("")
expect(registry.entries[0].address_editing).to_be(true)
expect(registry.entries[0].address_replace_on_text).to_be(false)
expect(registry.document_url(62)).to_equal(registry_url)
expect(
    registry.entries[0].renderer.pending_operation
).to_equal(registry_operation)
expect(_pixels_equal(
    registry.entries[0].pending_frame.pixels, registry_pixels
)).to_be(true)

val hosted_second = hosted.dispatch_key(7, 8, true)
val worker_second = worker.handle(BrowserRendererMessage(
    kind: "key", generation: 7, request_id: 5,
    payload: "K1\t2\t8\t1"
))
val registry_second = registry.dispatch_key_with_shift(
    8, 62, 8, true, false
)
expect(hosted_second.callback_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(hosted.address_text()).to_equal("")
expect(worker_second.ok).to_be(true)
expect(worker.browser.address_draft).to_equal("")
expect(registry_second.callback_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(registry.address_text(62)).to_equal("")

val hosted_typed = hosted.dispatch_text(9, "x")
val worker_typed = worker.handle(BrowserRendererMessage(
    kind: "text", generation: 7, request_id: 6,
    payload: "T1\t1\nx"
))
val registry_typed = registry.dispatch_text(10, 62, "x")
expect(hosted_typed.callback_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(hosted.address_text()).to_equal("x")
expect(worker_typed.ok).to_be(true)
expect(worker.browser.address_draft).to_equal("x")
expect(registry_typed.callback_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(registry.address_text(62)).to_equal("x")
expect(hosted.browser.current_url).to_equal(hosted_url)
expect(worker.browser.current_url).to_equal(worker_url)
expect(registry.document_url(62)).to_equal(registry_url)

expect(browser_address_backspace(
    "a한", false
).unwrap()).to_equal("a")
val malformed = rt_bytes_to_text([0xE2u8, 0x28u8, 0xA1u8])
val malformed_result = browser_address_backspace(malformed, true)
match malformed_result:
    Err(reason):
        expect(reason).to_equal("address-invalid-utf8")
    Ok(_):
        fail("malformed UTF-8 selection must fail closed")
expect(malformed).to_equal(
    rt_bytes_to_text([0xE2u8, 0x28u8, 0xA1u8])
)
expect(browser_address_backspace(
    "https://direct-entry.test/", true
).unwrap()).to_equal("")
val entry_source = file_read("src/os/hosted/hosted_entry.spl")
expect(entry_source.contains(
    "browser_address_backspace(\n" +
    "                                browser_address_draft,"
)).to_be(true)
expect(entry_source.contains(
    "browser_address_draft = text_without_last_codepoint("
)).to_be(false)
expect(registry.close()).to_be(true)
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


## Related Documentation

- **Requirements:** `REQ-WEB-BROWSER-007, REQ-WEB-BROWSER-008`


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a42d2ae39a5eb76f9c048ff856e32308451020636be7018f50ad36bf9fd2a441`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a42d2ae39a5eb76f9c048ff856e32308451020636be7018f50ad36bf9fd2a441`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a42d2ae39a5eb76f9c048ff856e32308451020636be7018f50ad36bf9fd2a441`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/browser/feature/browser_address_selection_backspace_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/browser_address_selection_backspace_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/browser/feature/browser_address_selection_backspace_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/browser/feature/browser_address_selection_backspace_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/browser_address_selection_backspace_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser/feature/browser_address_selection_backspace_spec.spl:58:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should clear the selected address without changing the committed page' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
