# JavaScript Error Side-Effect Preservation

> Verifies the browser eval error side effects behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# JavaScript Error Side-Effect Preservation

Verifies the browser eval error side effects behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/browser/feature/browser_eval_error_side_effects_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the browser eval error side effects behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### JavaScript error side-effect preservation

#### should preserve pre-error storage and cookies across isolated history traversal

- Verify: should preserve pre-error storage and cookies across isolated history traversal
- Open origin A
- Commit origin A writes before JavaScript throws
   - Expected: error equals `after-write`
   - Expected: session.local_storage_by_origin.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: session.local_storage_by_origin[0].entries.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: session.session_storage_by_origin.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: session.session_storage_by_origin[0].entries.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: session.cookies.count() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: session.document_cookie() equals `sid=A`
- Navigate to isolated origin B and commit different values
   - Expected: session.local_storage_item("key") ?? "" equals `B`
   - Expected: session.session_storage_item("key") ?? "" equals `B`
   - Expected: session.document_cookie() equals `sid=B`
   - Expected: session.local_storage_by_origin.len() equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: session.session_storage_by_origin.len() equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: session.cookies.count() equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: session.history.len() equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: session.current_index equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: session.history[0].url equals `https://a.example/page`
   - Expected: session.history[1].url equals `https://b.example/page`
- Go Back and observe origin A values from JavaScript
   - Expected: session.current_index equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: session.current_url equals `https://a.example/page`
   - Expected: session.history.len() equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: session.local_storage_by_origin.len() equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: session.session_storage_by_origin.len() equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: session.cookies.count() equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: value equals `A:A:sid=A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 93 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-005 REQ-WEB-BROWSER-009 REQ-WEB-BROWSER-012 REQ-WEB-BROWSER-013 REQ-WEB-BROWSER-021
step("Verify: should preserve pre-error storage and cookies across isolated history traversal")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Open origin A")
var session = BrowserSession.new()
expect(session.open_html(
    "https://a.example/page",
    "<html><body>Origin A</body></html>"
).is_ok()).to_be(true)

step("Commit origin A writes before JavaScript throws")
val failed = session.eval_script(
    "localStorage.setItem('key', 'A'); sessionStorage.setItem('key', 'A'); document.cookie = 'sid=A; Path=/'; throw 'after-write'"
)
match failed:
    Err(error):
        expect(error).to_equal("after-write")
    Ok(_):
        fail("Expected JavaScript to report after-write")
expect(session.local_storage_by_origin.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(session.local_storage_by_origin[0].origin).to_equal(
    "https://a.example"
)
expect(session.local_storage_by_origin[0].entries.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(session.local_storage_by_origin[0].entries[0].first).to_equal(
    "key"
)
expect(session.local_storage_by_origin[0].entries[0].second).to_equal(
    "A"
)
expect(session.session_storage_by_origin.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(session.session_storage_by_origin[0].origin).to_equal(
    "https://a.example"
)
expect(session.session_storage_by_origin[0].entries.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(session.session_storage_by_origin[0].entries[0].first).to_equal(
    "key"
)
expect(session.session_storage_by_origin[0].entries[0].second).to_equal(
    "A"
)
expect(session.cookies.count()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(session.document_cookie()).to_equal("sid=A")

step("Navigate to isolated origin B and commit different values")
expect(session.open_html(
    "https://b.example/page",
    "<html><body>Origin B</body></html>"
).is_ok()).to_be(true)
expect(session.eval_script(
    "localStorage.setItem('key', 'B'); sessionStorage.setItem('key', 'B'); document.cookie = 'sid=B; Path=/'; 'committed'"
).is_ok()).to_be(true)
expect(session.local_storage_item("key") ?? "").to_equal("B")
expect(session.session_storage_item("key") ?? "").to_equal("B")
expect(session.document_cookie()).to_equal("sid=B")
expect(session.local_storage_by_origin.len()).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(session.local_storage_by_origin[0].origin).to_equal(
    "https://a.example"
)
expect(session.local_storage_by_origin[1].origin).to_equal(
    "https://b.example"
)
expect(session.session_storage_by_origin.len()).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(session.session_storage_by_origin[0].origin).to_equal(
    "https://a.example"
)
expect(session.session_storage_by_origin[1].origin).to_equal(
    "https://b.example"
)
expect(session.cookies.count()).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(session.history.len()).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(session.current_index).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(session.history[0].url).to_equal("https://a.example/page")
expect(session.history[1].url).to_equal("https://b.example/page")

step("Go Back and observe origin A values from JavaScript")
expect(session.go_back().is_ok()).to_be(true)
expect(session.current_index).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(session.current_url).to_equal("https://a.example/page")
expect(session.history.len()).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(session.local_storage_by_origin.len()).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(session.session_storage_by_origin.len()).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(session.cookies.count()).to_equal(2)  # oracle: pinned constant asserted by this scenario
val restored = session.eval_script(
    "localStorage.getItem('key') + ':' + sessionStorage.getItem('key') + ':' + document.cookie"
)
match restored:
    Ok(JsValue.String(value)):
        expect(value).to_equal("A:A:sid=A")
    Ok(_):
        fail("Expected restored JavaScript values to be text")
    Err(error):
        fail("Expected restored JavaScript values: {error}")
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

- Canonical SPipe generation for source `7964ba9640157b189e5274043041b1d5b10111b40f423d5eae571d67f52dbb3f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7964ba9640157b189e5274043041b1d5b10111b40f423d5eae571d67f52dbb3f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7964ba9640157b189e5274043041b1d5b10111b40f423d5eae571d67f52dbb3f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/browser/feature/browser_eval_error_side_effects_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/browser_eval_error_side_effects_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/browser/feature/browser_eval_error_side_effects_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/browser/feature/browser_eval_error_side_effects_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/browser_eval_error_side_effects_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser/feature/browser_eval_error_side_effects_spec.spl:35:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve pre-error storage and cookies across isolated history traversal' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
