# Generation-qualified browser DOM identity

> Verifies the browser dom identity generation behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Generation-qualified browser DOM identity

Verifies the browser dom identity generation behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/browser/feature/browser_dom_identity_generation_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the browser dom identity generation behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Generation-qualified browser DOM identity

#### should retire stale routes across browser script UI and hosted rendering

- Verify: should retire stale routes across browser script UI and hosted rendering
   - Artifact capture: after_step
- Build the document identity index
   - Artifact capture: after_step
- Dispatch through stable routes
   - Artifact capture: after_step
- Replace the document during a handler
   - Artifact capture: after_step
- Reject stale routes and release the index
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-004 REQ-WEB-BROWSER-007 REQ-WEB-BROWSER-008 REQ-WEB-BROWSER-017 REQ-WEB-BROWSER-018
step("Verify: should retire stale routes across browser script UI and hosted rendering")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Build the document identity index")
val fixture = setup_dom_identity_generation_fixture()
check_dom_identity_index_built(fixture)

step("Dispatch through stable routes")
check_stable_route_dispatch(fixture)
_check_generation_preserving_and_structural_mutations()
_check_label_forwarding_and_rollback()
_check_shared_nested_dispatch_budget()

step("Replace the document during a handler")
_check_atomic_load_eval_and_index_rollback()
val replacement = check_document_replacement_during_handler(fixture)

step("Reject stale routes and release the index")
check_stale_routes_and_index_release(fixture, replacement)
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

- Canonical SPipe generation for source `1c9394513a1ccb2fbf712d75a90096c9a470b2dd3964e298f70b1790b3005413`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1c9394513a1ccb2fbf712d75a90096c9a470b2dd3964e298f70b1790b3005413`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1c9394513a1ccb2fbf712d75a90096c9a470b2dd3964e298f70b1790b3005413`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/browser/feature/browser_dom_identity_generation_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/browser_dom_identity_generation_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/browser/feature/browser_dom_identity_generation_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/browser/feature/browser_dom_identity_generation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/browser_dom_identity_generation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser/feature/browser_dom_identity_generation_spec.spl:867:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retire stale routes across browser script UI and hosted rendering' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
