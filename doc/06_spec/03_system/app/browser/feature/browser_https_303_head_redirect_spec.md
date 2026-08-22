# HTTPS 303 HEAD Redirect Semantics

> Verifies the browser https 303 head redirect behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HTTPS 303 HEAD Redirect Semantics

Verifies the browser https 303 head redirect behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/browser/feature/browser_https_303_head_redirect_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the browser https 303 head redirect behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### HTTPS 303 HEAD redirect semantics

#### should preserve HEAD without a body across a same-origin HTTPS 303

- Verify: should preserve HEAD without a body across a same-origin HTTPS 303
- Queue an HTTPS HEAD navigation
- Return a same-origin HTTPS 303
   - Expected: initial.method equals `HEAD`
- Take the redirected request
   - Expected: redirected.url equals `https://secure.test/final`
- Preserve HEAD redirect semantics
   - Expected: redirected.method equals `HEAD`
   - Expected: redirected.body equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: should preserve HEAD without a body across a same-origin HTTPS 303")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Queue an HTTPS HEAD navigation")
var session = BrowserSession.new()
expect(session.begin_network_navigation(
    "https://secure.test/start", "HEAD", "", "", ""
).is_ok()).to_be(true)

step("Return a same-origin HTTPS 303")
val initial = session.take_pending_request().unwrap()
expect(initial.method).to_equal("HEAD")
expect(session.commit_network_response(BrowserResponse.create(
    initial.id,
    "document",
    initial.url,
    303,
    "Location: /final\n",
    "",
    ""
)).is_ok()).to_be(true)

step("Take the redirected request")
val redirected = session.take_pending_request().unwrap()
expect(redirected.url).to_equal("https://secure.test/final")

step("Preserve HEAD redirect semantics")
expect(redirected.method).to_equal("HEAD")
expect(redirected.body).to_equal("")
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

- Canonical SPipe generation for source `14da99c49369ea70bc6a4c6951628be02df61abed0acc47dec75575be7a2174b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `14da99c49369ea70bc6a4c6951628be02df61abed0acc47dec75575be7a2174b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `14da99c49369ea70bc6a4c6951628be02df61abed0acc47dec75575be7a2174b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/browser/feature/browser_https_303_head_redirect_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/browser_https_303_head_redirect_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/browser/feature/browser_https_303_head_redirect_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/browser/feature/browser_https_303_head_redirect_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/browser_https_303_head_redirect_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser/feature/browser_https_303_head_redirect_spec.spl:32:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve HEAD without a body across a same-origin HTTPS 303' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
