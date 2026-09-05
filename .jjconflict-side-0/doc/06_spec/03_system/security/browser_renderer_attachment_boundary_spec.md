# Browser renderer attachment boundary

> Top-level attachment responses remain parent-owned download candidates. Until

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser renderer attachment boundary

Top-level attachment responses remain parent-owned download candidates. Until

## At a Glance

| Field | Value |
|-------|-------|
| Category | Security |
| Status | Active |
| Source | `test/03_system/security/browser_renderer_attachment_boundary_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Top-level attachment responses remain parent-owned download candidates. Until
a download subsystem exists, the hosted parent and BrowserSession independently
reject them without activating HTML or changing the committed page.

## Scenarios

### Browser renderer attachment boundary

#### should preserve the committed document when navigation is an attachment

- should preserve the committed document when navigation is an attachment
   - Protocol capture: after_step
- Install a safe document and attachment authority
   - Protocol capture: after_step
- Navigate through the hosted parent
   - Protocol capture: after_step
- Deliver an attachment document response
   - Protocol capture: after_step
- Preserve the committed document and reject activation
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the committed document when navigation is an attachment")
step("Install a safe document and attachment authority")
val fixture = setup_hosted_attachment_navigation_fixture()

step("Navigate through the hosted parent")
submit_attachment_navigation(fixture)

step("Deliver an attachment document response")
deliver_attachment_document_response(fixture)

step("Preserve the committed document and reject activation")
check_attachment_navigation_not_activated(fixture)
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
- `REQ-WEB-BROWSER-005`
- `REQ-WEB-BROWSER-010`
- `REQ-WEB-BROWSER-012`
- `REQ-WEB-BROWSER-021`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b81bfac0d978a1bdbc218ae0ba18811459adcdc6e4aaa8a5be3117171c5934c5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b81bfac0d978a1bdbc218ae0ba18811459adcdc6e4aaa8a5be3117171c5934c5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b81bfac0d978a1bdbc218ae0ba18811459adcdc6e4aaa8a5be3117171c5934c5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/security/browser_renderer_attachment_boundary_spec.spl
mirror: doc/06_spec/03_system/security/browser_renderer_attachment_boundary_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=95 oracle=100
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=88; blocker cap makes effective=49
doc/06_spec/03_system/security/browser_renderer_attachment_boundary_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/security/browser_renderer_attachment_boundary_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/security/browser_renderer_attachment_boundary_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 4 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/security/browser_renderer_attachment_boundary_spec.spl:279:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve the committed document when navigation is an attachment' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/security/browser_renderer_attachment_boundary_spec.spl:279:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve the committed document when navigation is an attachment' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
