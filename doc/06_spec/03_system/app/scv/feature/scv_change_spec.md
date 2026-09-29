# Scv Change Specification

> Tests covering REQ-003 stable change ids.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_change_spec

## Scenarios

### REQ-003 stable change ids

#### keeps a logical change id across state rewrites

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
# @req REQ-003
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/scv/feature/scv_change_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the scv change behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

Tests covering REQ-003 stable change ids.
- REQ-003 stable change ids

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
- `REQ-003`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e21105f5b2c1951bc7626bc1e591a058410079ba0f6c089731ff5ce827fa959b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e21105f5b2c1951bc7626bc1e591a058410079ba0f6c089731ff5ce827fa959b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e21105f5b2c1951bc7626bc1e591a058410079ba0f6c089731ff5ce827fa959b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/scv/feature/scv_change_spec.spl
mirror: doc/06_spec/03_system/app/scv/feature/scv_change_spec.md (current)
findings: 4 blockers: 1
  narrative=100 structure=90 oracle=50
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=85; blocker cap makes effective=49
doc/06_spec/03_system/app/scv/feature/scv_change_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/scv/feature/scv_change_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/scv/feature/scv_change_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/03_system/app/scv/feature/scv_change_spec.spl:35:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'keeps a logical change id across state rewrites' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
