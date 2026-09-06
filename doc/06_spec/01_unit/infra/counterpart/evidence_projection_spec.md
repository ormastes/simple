# Counterpart runs projected as Modern SSpec typed evidence (Lane F8)

> For QA authors writing counterpart-conformance scenarios: this spec documents

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Counterpart runs projected as Modern SSpec typed evidence (Lane F8)

For QA authors writing counterpart-conformance scenarios: this spec documents

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Wave 1 of doc/03_plan/infra/counterpart/counterpart_conformance_parallel_agent_plan_2026-08-09.md |
| Source | `test/01_unit/infra/counterpart/evidence_projection_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

For QA authors writing counterpart-conformance scenarios: this spec documents
what a counterpart run looks like once it reaches the ordinary typed-evidence
comparator, and — more importantly — what it looks like when the run did not
actually compare anything.

## Primary Workflow

A `CounterpartRun` is projected to `CanonicalEvidence` by
`counterpart_run_to_evidence`, then checked with the same
`compare_evidence` / `oracle_spec` machinery every other evidence kind uses.
The canonical path list in design section 13 is the contract: a scenario
asserts `counterpart.comparisons.failed == 0` and needs no new language.

## What must never happen

A run that executed nothing, compared nothing, or leaned on a single
independence group must NOT project as a clean node set. An empty-but-valid
node set satisfies a subset oracle and reads as a pass, so such a run is
projected as a parse failure instead. Likewise an unavailable provider is
projected with its real status; it is never absorbed into a pass.

## Scenarios

### Projecting a healthy counterpart run

#### emits every canonical evidence path declared in design section 13

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- emits every canonical evidence path declared in design section 13
- Project a run with two executed providers and one matched comparison
- Check each declared path resolves to its recorded value
   - Expected: result.status equals `EvidenceStatus.passed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("emits every canonical evidence path declared in design section 13")
step("Project a run with two executed providers and one matched comparison")
val evidence = counterpart_run_to_evidence(healthy_run())
assert_true(evidence.parse_ok)

step("Check each declared path resolves to its recorded value")
val result = compare_evidence(evidence, oracle_spec_open(
    PLAN_ID,
    [
        check_exact("counterpart.plan.id", PLAN_ID),
        check_exact("counterpart.boundary.id", BOUNDARY),
        check_exact("counterpart.providers.requested", "2"),
        check_exact("counterpart.providers.executed", "2"),
        check_exact("counterpart.providers.unavailable", "0"),
        check_exact("counterpart.comparisons.executed", "1"),
        check_exact("counterpart.comparisons.failed", "0"),
        check_exact("counterpart.provider.simple_gpu.status", "executed"),
        check_exact("counterpart.provider.simple_gpu.independence_group", "vulkan-stack"),
        check_exact("counterpart.matrix.simple_cpu.simple_gpu.relation", "canonical_exact"),
        check_exact("counterpart.matrix.simple_cpu.simple_gpu.matched", "true"),
        check_exact("counterpart.matrix.simple_cpu.simple_gpu.mismatch_count", "0"),
        check_exact("counterpart.execution.simple_gpu.mode", "vulkan"),
        check_exact("counterpart.execution.simple_gpu.submission_count", "3"),
        check_exact("counterpart.execution.simple_gpu.fence_completed", "true"),
        check_exact("counterpart.execution.simple_gpu.device_origin_readback", "true"),
        check_exact("counterpart.execution.simple_gpu.fallback_used", "false")
    ]
))
expect(result.status).to_equal(EvidenceStatus.passed)
```

</details>

#### fails the same evidence against a wrong oracle

- fails the same evidence against a wrong oracle
- Assert a fallback_used value the receipt does not carry
   - Expected: result.status equals `EvidenceStatus.failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("fails the same evidence against a wrong oracle")
step("Assert a fallback_used value the receipt does not carry")
val evidence = counterpart_run_to_evidence(healthy_run())
val result = compare_evidence(evidence, oracle_spec_open(
    PLAN_ID,
    [check_exact("counterpart.execution.simple_gpu.fallback_used", "true")]
))
expect(result.status).to_equal(EvidenceStatus.failed)
```

</details>

### Refusing to project a vacuous run

#### projects a run with zero comparisons as a parse failure, not clean nodes

- projects a run with zero comparisons as a parse failure, not clean nodes
- Take a healthy run and remove every comparison
- Project it
- The projection must be a parse failure carrying the gate reason
- And it must fail the comparator even against an oracle it would otherwise satisfy
   - Expected: result.status equals `EvidenceStatus.failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("projects a run with zero comparisons as a parse failure, not clean nodes")
step("Take a healthy run and remove every comparison")
var run = healthy_run()
run.matrix = []

step("Project it")
val evidence = counterpart_run_to_evidence(run)

step("The projection must be a parse failure carrying the gate reason")
assert_false(evidence.parse_ok)
assert_equal(evidence.nodes.len(), 0)
assert_true(evidence.parse_error.contains("zero comparisons"))

step("And it must fail the comparator even against an oracle it would otherwise satisfy")
val result = compare_evidence(evidence, oracle_spec_open(
    PLAN_ID,
    [check_exact("counterpart.comparisons.failed", "0")]
))
expect(result.status).to_equal(EvidenceStatus.failed)
```

</details>

#### projects a run with no executed source as a parse failure

- projects a run with no executed source as a parse failure
- Mark every source unavailable
- Project it and read the blockers


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("projects a run with no executed source as a parse failure")
step("Mark every source unavailable")
var run = healthy_run()
var a = run.sources[0]
var b = run.sources[1]
a.status = ProviderStatus.unavailable
b.status = ProviderStatus.unavailable
run.sources = [a, b]

step("Project it and read the blockers")
val evidence = counterpart_run_to_evidence(run)
assert_false(evidence.parse_ok)
assert_true(projection_blockers(run).len() > 0)
```

</details>

#### projects a run whose sources share one independence group as a failure

- projects a run whose sources share one independence group as a failure
- Give both executed sources the same independence group


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("projects a run whose sources share one independence group as a failure")
step("Give both executed sources the same independence group")
var run = healthy_run()
var a = run.sources[0]
var b = run.sources[1]
a.independence_group = "simple"
b.independence_group = "simple"
run.sources = [a, b]

val evidence = counterpart_run_to_evidence(run)
assert_false(evidence.parse_ok)
assert_true(evidence.parse_error.contains("independence group"))
```

</details>

### An unavailable provider is never a pass

#### records the unavailable status instead of absorbing it

- records the unavailable status instead of absorbing it
- Add a third provider that could not run
- Its status and the unavailable count are both projected as data
   - Expected: recorded.status equals `EvidenceStatus.passed`
- So the design's clean-run oracle FAILS on this run
   - Expected: clean.status equals `EvidenceStatus.failed`
- And the unavailable provider is never reported as executed
   - Expected: mislabelled.status equals `EvidenceStatus.failed`
- The full frozen gate still names it, for lanes whose plan requires it


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("records the unavailable status instead of absorbing it")
step("Add a third provider that could not run")
val evidence = counterpart_run_to_evidence(unavailable_run())
assert_true(evidence.parse_ok)

step("Its status and the unavailable count are both projected as data")
val recorded = compare_evidence(evidence, oracle_spec_open(
    PLAN_ID,
    [
        check_exact("counterpart.provider.reference.status", "unavailable"),
        check_exact("counterpart.providers.requested", "3"),
        check_exact("counterpart.providers.executed", "2"),
        check_exact("counterpart.providers.unavailable", "1")
    ]
))
expect(recorded.status).to_equal(EvidenceStatus.passed)

step("So the design's clean-run oracle FAILS on this run")
val clean = compare_evidence(evidence, oracle_spec_open(
    PLAN_ID,
    [check_exact("counterpart.providers.unavailable", "0")]
))
expect(clean.status).to_equal(EvidenceStatus.failed)

step("And the unavailable provider is never reported as executed")
val mislabelled = compare_evidence(evidence, oracle_spec_open(
    PLAN_ID,
    [check_exact("counterpart.provider.reference.status", "executed")]
))
expect(mislabelled.status).to_equal(EvidenceStatus.failed)

step("The full frozen gate still names it, for lanes whose plan requires it")
assert_true(strict_vacuity_failures(unavailable_run()).len() > 0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-COUNTERPART-EVID-001`
- `REQ-SSPEC-INFRA`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f747451314551addb9f07c18fc840fbe15c87d9754d63aaf02a0b46c344d34a9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f747451314551addb9f07c18fc840fbe15c87d9754d63aaf02a0b46c344d34a9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f747451314551addb9f07c18fc840fbe15c87d9754d63aaf02a0b46c344d34a9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/infra/counterpart/evidence_projection_spec.spl
mirror: doc/06_spec/01_unit/infra/counterpart/evidence_projection_spec.md (current)
findings: 3 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=91; blocker cap makes effective=49
doc/06_spec/01_unit/infra/counterpart/evidence_projection_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/infra/counterpart/evidence_projection_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/infra/counterpart/evidence_projection_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
<!-- sspec-maintain:scorecard:end -->
