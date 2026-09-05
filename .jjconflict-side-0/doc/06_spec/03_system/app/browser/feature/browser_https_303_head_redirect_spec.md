# HTTPS 303 HEAD Redirect Semantics

> An HTTPS `303 See Other` must preserve a metadata-only `HEAD` navigation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HTTPS 303 HEAD Redirect Semantics

An HTTPS `303 See Other` must preserve a metadata-only `HEAD` navigation.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/browser/feature/browser_https_303_head_redirect_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

An HTTPS `303 See Other` must preserve a metadata-only `HEAD` navigation.
The redirected request stays encrypted, carries no body, and does not silently
become a content-fetching `GET`.

## Scenarios

### HTTPS 303 HEAD redirect semantics

#### should preserve HEAD without a body across a same-origin HTTPS 303

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should preserve HEAD without a body across a same-origin HTTPS 303
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

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve HEAD without a body across a same-origin HTTPS 303")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-WEB-BROWSER-010`
- `REQ-WEB-BROWSER-011`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `be4c390779148af78b5b97e2dbd8a74cd846a3fdeb57fc031afed7bcb49d6f40`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `be4c390779148af78b5b97e2dbd8a74cd846a3fdeb57fc031afed7bcb49d6f40`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `be4c390779148af78b5b97e2dbd8a74cd846a3fdeb57fc031afed7bcb49d6f40`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/browser/feature/browser_https_303_head_redirect_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/browser_https_303_head_redirect_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=95 oracle=100
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=88; blocker cap makes effective=49
doc/06_spec/03_system/app/browser/feature/browser_https_303_head_redirect_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/browser_https_303_head_redirect_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser/feature/browser_https_303_head_redirect_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/app/browser/feature/browser_https_303_head_redirect_spec.spl:22:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve HEAD without a body across a same-origin HTTPS 303' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/browser/feature/browser_https_303_head_redirect_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve HEAD without a body across a same-origin HTTPS 303' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
