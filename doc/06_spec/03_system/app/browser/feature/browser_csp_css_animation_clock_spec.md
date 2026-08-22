# CSP-Denied Script CSS Animation Clock

> Verifies the browser csp css animation clock behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CSP-Denied Script CSS Animation Clock

Verifies the browser csp css animation clock behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/browser/feature/browser_csp_css_animation_clock_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the browser csp css animation clock behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### REQ-WEB-BROWSER-003/004/005/006/012: CSP animation clock

#### should advance CSS animation frames while scripts stay denied

- Verify: should advance CSS animation frames while scripts stay denied
   - Artifact capture: after_step
- Commit a script-denying CSP
   - Artifact capture: after_step
- Advance the monotonic browser clock
   - Artifact capture: after_step
- Reject script callbacks
   - Artifact capture: after_step
- Render the next CSS animation frame
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-003/004/005/006/012
# @req: REQ-WEB-BROWSER-003 REQ-WEB-BROWSER-004 REQ-WEB-BROWSER-005 REQ-WEB-BROWSER-006 REQ-WEB-BROWSER-012 REQ-WEB-BROWSER-021
step("Verify: should advance CSS animation frames while scripts stay denied")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Commit a script-denying CSP")
val session = setup_csp_clock_fixture()
step("Advance the monotonic browser clock")
check_clock_advanced_without_callbacks(session)
step("Reject script callbacks")
check_scripts_denied(session)
step("Render the next CSS animation frame")
check_css_frame_progressed(session)
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

- Canonical SPipe generation for source `b8311e9d03c1d2e7d1190711596e6c62eaf3e66b4fe779f54d5b190a3b0daec3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b8311e9d03c1d2e7d1190711596e6c62eaf3e66b4fe779f54d5b190a3b0daec3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b8311e9d03c1d2e7d1190711596e6c62eaf3e66b4fe779f54d5b190a3b0daec3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/browser/feature/browser_csp_css_animation_clock_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/browser_csp_css_animation_clock_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/browser/feature/browser_csp_css_animation_clock_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/browser/feature/browser_csp_css_animation_clock_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/browser_csp_css_animation_clock_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser/feature/browser_csp_css_animation_clock_spec.spl:178:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should advance CSS animation frames while scripts stay denied' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
