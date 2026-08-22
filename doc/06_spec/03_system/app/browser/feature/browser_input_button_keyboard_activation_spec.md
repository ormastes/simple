# Hosted input-button keyboard activation

> Verifies the browser input button keyboard activation behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hosted input-button keyboard activation

Verifies the browser input button keyboard activation behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/browser/feature/browser_input_button_keyboard_activation_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the browser input button keyboard activation behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Hosted input-button keyboard activation

#### should preserve keyboard pointer and form semantics

- Verify: should preserve keyboard pointer and form semantics
   - HTML capture: after_step
- Install hosted input-button activation controls
   - HTML capture: after_step
- Focus input buttons through the host Tab route
   - HTML capture: after_step
- Activate the focused controls with Space and Enter
   - HTML capture: after_step
- Preserve pointer parity and form non-submission
   - HTML capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-005 REQ-WEB-BROWSER-007 REQ-WEB-BROWSER-008
step("Verify: should preserve keyboard pointer and form semantics")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Install hosted input-button activation controls")
var fixture = setup_hosted_input_button_activation_fixture()

step("Focus input buttons through the host Tab route")
focus_input_buttons_through_host_tab(fixture)

step("Activate the focused controls with Space and Enter")
activate_input_buttons_through_host_keyboard(fixture)

step("Preserve pointer parity and form non-submission")
check_input_button_activation_and_form_safety(fixture)
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

- Canonical SPipe generation for source `dfd22fc654935059f5a91dae7618a74f2e562b9d17cfa996cfbf09d15dd9b153`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dfd22fc654935059f5a91dae7618a74f2e562b9d17cfa996cfbf09d15dd9b153`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dfd22fc654935059f5a91dae7618a74f2e562b9d17cfa996cfbf09d15dd9b153`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/browser/feature/browser_input_button_keyboard_activation_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/browser_input_button_keyboard_activation_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/browser/feature/browser_input_button_keyboard_activation_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/browser/feature/browser_input_button_keyboard_activation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/browser_input_button_keyboard_activation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser/feature/browser_input_button_keyboard_activation_spec.spl:173:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve keyboard pointer and form semantics' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
