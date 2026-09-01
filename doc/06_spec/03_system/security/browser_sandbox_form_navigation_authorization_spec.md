# Browser Sandbox Form Navigation Authorization

> Proves with local typed HTTPS fixtures that `allow-forms` does not grant

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Sandbox Form Navigation Authorization

Proves with local typed HTTPS fixtures that `allow-forms` does not grant

## At a Glance

| Field | Value |
|-------|-------|
| Category | Security |
| Status | Active |
| Source | `test/03_system/security/browser_sandbox_form_navigation_authorization_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Proves with local typed HTTPS fixtures that `allow-forms` does not grant
top-level navigation. A denied submission cannot queue or leak its POST body
and cannot replace the authorized document's Draw IR or final pixels. The
positive control retains the canonical form request path when both sandbox
capabilities are present.

## Scenarios

### REQ-WEB-BROWSER-012: sandboxed form navigation authorization

#### should render only the document authorized for top navigation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
# @req REQ-WEB-BROWSER-012
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
- `REQ-WEB-BROWSER-012`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2a14d607c3ee6bada9b7c2aa2fc5e3b5a2e04ca953563d0e0b031b75041626ac`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2a14d607c3ee6bada9b7c2aa2fc5e3b5a2e04ca953563d0e0b031b75041626ac`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2a14d607c3ee6bada9b7c2aa2fc5e3b5a2e04ca953563d0e0b031b75041626ac`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/security/browser_sandbox_form_navigation_authorization_spec.spl
mirror: doc/06_spec/03_system/security/browser_sandbox_form_navigation_authorization_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=85 oracle=50
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/03_system/security/browser_sandbox_form_navigation_authorization_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/security/browser_sandbox_form_navigation_authorization_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/security/browser_sandbox_form_navigation_authorization_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/03_system/security/browser_sandbox_form_navigation_authorization_spec.spl:53:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should render only the document authorized for top navigation' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/security/browser_sandbox_form_navigation_authorization_spec.spl:53:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should render only the document authorized for top navigation' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
