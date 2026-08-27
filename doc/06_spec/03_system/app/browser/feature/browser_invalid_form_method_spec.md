# browser_invalid_form_method_spec

> Invalid HTML form-method fallback system specification.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# browser_invalid_form_method_spec

Invalid HTML form-method fallback system specification.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/browser/feature/browser_invalid_form_method_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Invalid HTML form-method fallback system specification.

The selected profile supports GET and POST. Invalid method tokens are not a
transport permission and therefore fall back to GET before the independent
navigation boundary evaluates the action URL.

## Scenarios

### BrowserSession invalid form method fallback

#### should use GET for invalid method tokens without widening transport

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
# @req REQ-WEB-BROWSER-007
# @req REQ-WEB-BROWSER-008
# @req REQ-WEB-BROWSER-010
# @req REQ-WEB-BROWSER-012
# @req REQ-WEB-BROWSER-021
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
- `REQ-WEB-BROWSER-007`
- `REQ-WEB-BROWSER-008`
- `REQ-WEB-BROWSER-010`
- `REQ-WEB-BROWSER-012`
- `REQ-WEB-BROWSER-021`
- `REQ-WEB-BROWSER-007:`
- `REQ-WEB-BROWSER-008:`
- `REQ-WEB-BROWSER-010:`
- `REQ-WEB-BROWSER-012:`
- `REQ-WEB-BROWSER-021:`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1f87a72a5325587546db2069152de95ad1f68611ebb61721df90a9a691380ab3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1f87a72a5325587546db2069152de95ad1f68611ebb61721df90a9a691380ab3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1f87a72a5325587546db2069152de95ad1f68611ebb61721df90a9a691380ab3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/browser/feature/browser_invalid_form_method_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/browser_invalid_form_method_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=85 oracle=50
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/03_system/app/browser/feature/browser_invalid_form_method_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/browser_invalid_form_method_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser/feature/browser_invalid_form_method_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/03_system/app/browser/feature/browser_invalid_form_method_spec.spl:205:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should use GET for invalid method tokens without widening transport' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/browser/feature/browser_invalid_form_method_spec.spl:205:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should use GET for invalid method tokens without widening transport' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
