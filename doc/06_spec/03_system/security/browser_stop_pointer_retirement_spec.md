# Hosted Stop pointer retirement

> Proves that deferred Stop activation preserves the committed page and retained

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hosted Stop pointer retirement

Proves that deferred Stop activation preserves the committed page and retained

## At a Glance

| Field | Value |
|-------|-------|
| Category | Security |
| Status | Active |
| Source | `test/03_system/security/browser_stop_pointer_retirement_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Proves that deferred Stop activation preserves the committed page and retained
resources while retiring pointer ownership in both hosted parent and worker.
A release from the pre-Stop press is rejected before it can emit pointer-up or
reach the worker click path.

## Scenarios

### Hosted Stop pointer retirement

#### should reject a pre-Stop release without losing committed content

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should reject a pre-Stop release without losing committed content
- Prime a completed content pointer press
- Dispatch Stop through the hosted parent
- Acknowledge Stop in the renderer worker
- Reject the stale post-Stop release


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject a pre-Stop release without losing committed content")
step("Prime a completed content pointer press")
val fixture = setup_hosted_stop_pressed_fixture()

step("Dispatch Stop through the hosted parent")
submit_stop_with_pressed_pointer(fixture)

step("Acknowledge Stop in the renderer worker")
complete_hosted_stop(fixture)

step("Reject the stale post-Stop release")
check_stop_retires_pointer_state(fixture)
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
- `REQ-WEB-BROWSER-008`
- `REQ-WEB-BROWSER-009`
- `REQ-WEB-BROWSER-014`
- `REQ-WEB-BROWSER-018`
- `REQ-WEB-BROWSER-021`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a7fac680688ef0d70805aa580d8c4d0bc5da80669e04b3f72fde868a030b6213`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a7fac680688ef0d70805aa580d8c4d0bc5da80669e04b3f72fde868a030b6213`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a7fac680688ef0d70805aa580d8c4d0bc5da80669e04b3f72fde868a030b6213`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/security/browser_stop_pointer_retirement_spec.spl
mirror: doc/06_spec/03_system/security/browser_stop_pointer_retirement_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=95 oracle=100
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=88; blocker cap makes effective=49
doc/06_spec/03_system/security/browser_stop_pointer_retirement_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/security/browser_stop_pointer_retirement_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/security/browser_stop_pointer_retirement_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 5 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/security/browser_stop_pointer_retirement_spec.spl:149:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject a pre-Stop release without losing committed content' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/security/browser_stop_pointer_retirement_spec.spl:149:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject a pre-Stop release without losing committed content' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
