# Canceled Browser Text Editing

> Verifies the browser text edit cancellation behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Canceled Browser Text Editing

Verifies the browser text edit cancellation behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md |
| Plan | doc/03_plan/sys_test/simple_web_browser_engine_production_hardening.md |
| Design | doc/04_architecture/simple_web_browser_engine_production_hardening.md |
| Research | doc/01_research/local/simple_web_browser_engine_production_hardening.md |
| Source | `test/03_system/app/browser/feature/browser_text_edit_cancellation_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the browser text edit cancellation behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Canceled browser text editing

#### should preserve selection and event ordering across hosted and worker paths

- Verify: should preserve selection and event ordering across hosted and worker paths
- Cancel hosted Backspace and Delete over the UTF-8 selection
   - Expected: hosted_backspace.semantic_target_id equals `q`
   - Expected: hosted_delete.semantic_target_id equals `q`
- Extend the retained hosted selection and clear it on blur
   - Expected: hosted_shift_right.semantic_target_id equals `q`
- Cancel worker K2 Backspace and Delete over the same selection
- Extend the retained worker selection and clear it on blur


<details>
<summary>Executable SSpec</summary>

Runnable source: 62 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-007 REQ-WEB-BROWSER-008
step("Verify: should preserve selection and event ordering across hosted and worker paths")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Cancel hosted Backspace and Delete over the UTF-8 selection")
var hosted = HostedWebContentSession.create(
    41, CANCELED_TEXT_EDIT_HTML, 80, 40
)
expect(hosted.browser.set_dom_text_selection("q", 1, 3)).to_be(true)
val hosted_backspace = hosted.dispatch_key_with_shift(
    1, 8, true, false
)
expect(hosted_backspace.semantic_target_id).to_equal("q")
expect_canceled_text_edit(hosted.browser, "beforeinput,")
expect(hosted.browser.set_dom_text_selection("q", 1, 3)).to_be(true)
val hosted_delete = hosted.dispatch_key_with_shift(
    2, 127, true, false
)
expect(hosted_delete.semantic_target_id).to_equal("q")
expect_canceled_text_edit(
    hosted.browser, "beforeinput,beforeinput,"
)

step("Extend the retained hosted selection and clear it on blur")
val hosted_shift_right = hosted.dispatch_key_with_shift(
    3, 39, true, true
)
expect(hosted_shift_right.semantic_target_id).to_equal("q")
expect_shift_extended_selection(hosted.browser)
expect_text_selection_cleanup(
    hosted.browser, "beforeinput,beforeinput,"
)

step("Cancel worker K2 Backspace and Delete over the same selection")
var worker = HostedBrowserRendererWorkerSession.create(80, 40)
expect(worker.handle(BrowserRendererMessage(
    kind: "init", generation: 7, request_id: 2,
    payload: CANCELED_TEXT_EDIT_HTML
)).ok).to_be(true)
expect(worker.browser.set_dom_text_selection("q", 1, 3)).to_be(true)
expect(worker.handle(BrowserRendererMessage(
    kind: "key", generation: 7, request_id: 3,
    payload: "K2\t1\t8\t1\t0"
)).ok).to_be(true)
expect_canceled_text_edit(worker.browser, "beforeinput,")
expect(worker.browser.set_dom_text_selection("q", 1, 3)).to_be(true)
expect(worker.handle(BrowserRendererMessage(
    kind: "key", generation: 7, request_id: 4,
    payload: "K2\t2\t127\t1\t0"
)).ok).to_be(true)
expect_canceled_text_edit(
    worker.browser, "beforeinput,beforeinput,"
)

step("Extend the retained worker selection and clear it on blur")
expect(worker.handle(BrowserRendererMessage(
    kind: "key", generation: 7, request_id: 5,
    payload: "K2\t3\t39\t1\t1"
)).ok).to_be(true)
expect_shift_extended_selection(worker.browser)
expect_text_selection_cleanup(
    worker.browser, "beforeinput,beforeinput,"
)
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

- **Requirements:** `doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md`
- **Plan:** `doc/03_plan/sys_test/simple_web_browser_engine_production_hardening.md`
- **Design:** `doc/04_architecture/simple_web_browser_engine_production_hardening.md`
- **Research:** `doc/01_research/local/simple_web_browser_engine_production_hardening.md`


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a4c9b7a9f4024218f5e2d6800f68faba2525012546a543bc9873d63a8403e43a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a4c9b7a9f4024218f5e2d6800f68faba2525012546a543bc9873d63a8403e43a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a4c9b7a9f4024218f5e2d6800f68faba2525012546a543bc9873d63a8403e43a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/browser/feature/browser_text_edit_cancellation_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/browser_text_edit_cancellation_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/browser/feature/browser_text_edit_cancellation_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/browser/feature/browser_text_edit_cancellation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/browser_text_edit_cancellation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser/feature/browser_text_edit_cancellation_spec.spl:179:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve selection and event ordering across hosted and worker paths' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
