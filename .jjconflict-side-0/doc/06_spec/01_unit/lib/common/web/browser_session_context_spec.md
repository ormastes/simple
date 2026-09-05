# Browser Session Context Specification

> Tests covering BrowserSession secure context.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Context Specification

## Scenarios

### BrowserSession secure context

<details>
<summary>Advanced: trusts exact loopback hosts without trusting prefix spoofs</summary>

#### trusts exact loopback hosts without trusting prefix spoofs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- trusts exact loopback hosts without trusting prefix spoofs


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("trusts exact loopback hosts without trusting prefix spoofs")
expect(browser_session_is_loopback_http(
    "http://localhost:8080/app"
)).to_equal(true)
expect(browser_session_is_loopback_http(
    "http://127.0.0.1/app"
)).to_equal(true)
expect(browser_session_is_loopback_http(
    "http://localhost.evil/app"
)).to_equal(false)
expect(browser_session_is_loopback_http(
    "http://127.0.0.1.evil/app"
)).to_equal(false)
expect(browser_session_is_secure_context(
    "http://localhost.evil/app"
)).to_equal(false)
```

</details>


</details>

#### ignores directives forbidden in meta CSP

- ignores directives forbidden in meta CSP


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("ignores directives forbidden in meta CSP")
expect(browser_meta_content_security_policy(
    "sandbox allow-scripts; frame-ancestors 'none'; report-uri /r; default-src 'self'"
)).to_equal("default-src 'self'")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_context_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BrowserSession secure context.
- BrowserSession secure context

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `23920a5ae08f96919ff0df0416773790cbba330c3eb76df0c3a1d3b6a89e16e2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `23920a5ae08f96919ff0df0416773790cbba330c3eb76df0c3a1d3b6a89e16e2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `23920a5ae08f96919ff0df0416773790cbba330c3eb76df0c3a1d3b6a89e16e2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/lib/common/web/browser_session_context_spec.spl
mirror: doc/06_spec/01_unit/lib/common/web/browser_session_context_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/web/browser_session_context_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/web/browser_session_context_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/web/browser_session_context_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'trusts exact loopback hosts without trusting prefix spoofs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/web/browser_session_context_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ignores directives forbidden in meta CSP' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
