# Generation-qualified browser DOM identity

> The real BrowserSession, textual UI adapter, SimpleScript bridge, hosted

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Generation-qualified browser DOM identity

The real BrowserSession, textual UI adapter, SimpleScript bridge, hosted

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/browser/feature/browser_dom_identity_generation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

The real BrowserSession, textual UI adapter, SimpleScript bridge, hosted
pointer adapter, canonical web Draw IR, and Engine2D executor share one
generation-qualified DOM route. Replacing the document during a handler
retires the old route before callbacks, defaults, or pointer release can
retarget an equal author or numeric identity.

The folded N/2N assertions prove exact two-pass work counters. The 10,000-cycle
receipt is schema-only and remains runtime-held until an admitted current
pure-Simple runner records timing, allocation, RSS, and lifecycle evidence.

## Scenarios

### Generation-qualified browser DOM identity

#### should retire stale routes across browser script UI and hosted rendering

- should retire stale routes across browser script UI and hosted rendering
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

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retire stale routes across browser script UI and hosted rendering")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3dfe32f5a76209997c2341f0f0735219cb9cce8fea546571da9158fc17ec50fb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3dfe32f5a76209997c2341f0f0735219cb9cce8fea546571da9158fc17ec50fb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3dfe32f5a76209997c2341f0f0735219cb9cce8fea546571da9158fc17ec50fb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/browser/feature/browser_dom_identity_generation_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/browser_dom_identity_generation_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/browser/feature/browser_dom_identity_generation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/browser_dom_identity_generation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser/feature/browser_dom_identity_generation_spec.spl:857:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retire stale routes across browser script UI and hosted rendering' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/browser/feature/browser_dom_identity_generation_spec.spl:857:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should retire stale routes across browser script UI and hosted rendering' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
