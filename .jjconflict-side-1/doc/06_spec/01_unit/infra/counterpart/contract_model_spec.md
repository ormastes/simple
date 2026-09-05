# Counterpart Conformance — frozen contracts

> The counterpart contracts decide, before any provider is loaded, whether a

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Counterpart Conformance — frozen contracts

The counterpart contracts decide, before any provider is loaded, whether a

## At a Glance

| Field | Value |
|-------|-------|
| Category | Infrastructure |
| Status | In Progress |
| Plan | doc/03_plan/infra/counterpart/counterpart_conformance_parallel_agent_plan_2026-08-09.md |
| Design | doc/05_design/infra/counterpart/counterpart_conformance_infrastructure_design_2026-08-09.md |
| Source | `test/01_unit/infra/counterpart/contract_model_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

The counterpart contracts decide, before any provider is loaded, whether a
conformance run is capable of proving anything at all. This scenario is for the
engineer adding a new provider, converter or domain lane: it shows the shape of
a plan the framework accepts, and — more usefully — the shapes it refuses.

## Scope and Preconditions

Pure records only. Nothing here loads an adapter, opens a library or reaches the
network; the checks are the fail-closed gates from the design document expressed
as data. No provider needs to be built to run this scenario.

## Primary Workflow

An operator declares a plan naming a candidate source and at least one oracle
source, then declares the comparisons between them. The framework answers with
the list of reasons the plan is unacceptable. An empty list means the plan is
admissible — not that the run passed.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Boundary ID | `<domain>.<mdsoc-layer>.<stage>@<schema-version>`; the only thing a plan names |
| Oracle authority | Ranks a source: a normative vector outranks any number of agreeing peers |
| Independence group | Two wrappers over one upstream engine count as ONE reference, not two |
| Execution receipt | Proves the GPU lane actually reached the GPU rather than falling back |
| Conversion loss | Ordered severity; an exact relation may not traverse a lossy route |

## Related Specifications

- `test/01_unit/infra/counterpart/converter_graph_spec.spl` — route resolution
- `test/01_unit/infra/counterpart/evidence_projection_spec.spl` — Modern SSpec projection

## Evidence and Provenance

Contracts frozen 2026-08-09 by the Wave-0 ADR. Every rejection asserted below
maps to a numbered acceptance gate in the design document's final table.

## Recovery and Troubleshooting

A rejection message names the offending source or comparison by ID. A plan that
is admissible but still yields no comparisons fails later, at the vacuity gate —
the two are deliberately separate so an empty run cannot read as a clean one.

## Compatibility and Limitations

These are contracts, not execution. Passing here proves a malformed plan is
refused; it proves nothing about any provider, adapter or converter.

## Scenarios

### Counterpart plan admission

#### accepts a plan naming a candidate and an independent reference

- accepts a plan naming a candidate and an independent reference
- Declare a plan with one candidate source and one reference source
- Ask the framework for its reasons to refuse the plan
- Confirm the plan is admissible
   - Expected: rejections.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("accepts a plan naming a candidate and an independent reference")
step("Declare a plan with one candidate source and one reference source")
val plan = a_wellformed_plan()
step("Ask the framework for its reasons to refuse the plan")
val rejections = counterpart_plan_rejections(plan)
step("Confirm the plan is admissible")
expect(rejections.len()).to_equal(0)
```

</details>

#### round-trips a boundary identifier through its text form

- round-trips a boundary identifier through its text form
- Parse the canonical boundary identifier
- Confirm each component was recovered
   - Expected: parsed.domain equals `web`
   - Expected: parsed.layer equals `spatial_layout`
   - Expected: parsed.stage equals `fragment_table`
   - Expected: parsed.schema_version equals `1`
- Confirm the text form is stable
   - Expected: boundary_id_text(parsed) equals `web.spatial_layout.fragment_table@1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("round-trips a boundary identifier through its text form")
step("Parse the canonical boundary identifier")
val parsed = parse_boundary_id("web.spatial_layout.fragment_table@1")
step("Confirm each component was recovered")
expect(parsed.domain).to_equal("web")
expect(parsed.layer).to_equal("spatial_layout")
expect(parsed.stage).to_equal("fragment_table")
expect(parsed.schema_version).to_equal(1)
step("Confirm the text form is stable")
expect(boundary_id_text(parsed)).to_equal("web.spatial_layout.fragment_table@1")
```

</details>

### Counterpart plan refusals

#### refuses a boundary identifier with no schema version

- refuses a boundary identifier with no schema version
- Parse an identifier that omits its schema version
- Confirm it is rejected rather than defaulted to version 1
   - Expected: parsed.schema_version equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses a boundary identifier with no schema version")
step("Parse an identifier that omits its schema version")
val parsed = parse_boundary_id("web.resolve.computed_style")
step("Confirm it is rejected rather than defaulted to version 1")
assert_false(boundary_id_is_valid(parsed))
expect(parsed.schema_version).to_equal(-1)
```

</details>

#### refuses a plan whose only sources are diagnostic

- refuses a plan whose only sources are diagnostic
- Declare a plan whose sources carry no binding authority
- Confirm the framework refuses to treat diagnostics as an oracle


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses a plan whose only sources are diagnostic")
step("Declare a plan whose sources carry no binding authority")
val plan = counterpart_plan(
    "counterpart.web.style.v1",
    "web.resolve.computed_style@1",
    "web-pinned-deterministic",
    "fixture.html",
    [
        plan_source("a", "p", "c", OracleAuthority.diagnostic_only, true),
        plan_source("b", "q", "c", OracleAuthority.diagnostic_only, true)
    ],
    [plan_comparison("a", "b", CounterpartRelation.canonical_exact)]
)
step("Confirm the framework refuses to treat diagnostics as an oracle")
val rejections = counterpart_plan_rejections(plan)
expect(rejections.len()).to_be_greater_than(0)
```

</details>

#### refuses a plan that declares zero comparisons

- refuses a plan that declares zero comparisons
- Declare a plan with sources but no comparisons between them
- Confirm the empty matrix is refused, not silently passed


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses a plan that declares zero comparisons")
step("Declare a plan with sources but no comparisons between them")
val plan = counterpart_plan(
    "counterpart.web.style.v1",
    "web.resolve.computed_style@1",
    "web-pinned-deterministic",
    "fixture.html",
    [a_candidate_source(), an_independent_reference()],
    []
)
step("Confirm the empty matrix is refused, not silently passed")
val rejections = counterpart_plan_rejections(plan)
expect(rejections.len()).to_be_greater_than(0)
```

</details>

#### refuses a numeric tolerance that states no reason

- refuses a numeric tolerance that states no reason
- Declare a comparison carrying an unexplained tolerance
- Confirm an unexplained tolerance is treated as a fabricated expectation


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses a numeric tolerance that states no reason")
step("Declare a comparison carrying an unexplained tolerance")
val plan = counterpart_plan(
    "counterpart.web.layout.v1",
    "web.spatial_layout.fragment_table@1",
    "web-pinned-deterministic",
    "fixture.html",
    [a_candidate_source(), an_independent_reference()],
    [plan_comparison_with_tolerance(
        "simple_cpu", "chrome", CounterpartRelation.numeric_bound, 2, "")]
)
step("Confirm an unexplained tolerance is treated as a fabricated expectation")
val rejections = counterpart_plan_rejections(plan)
expect(rejections.len()).to_be_greater_than(0)
```

</details>

#### refuses a comparison of a source against itself

- refuses a comparison of a source against itself
- Declare a comparison whose two sides are the same source
- Confirm the self-comparison is refused


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses a comparison of a source against itself")
step("Declare a comparison whose two sides are the same source")
val plan = counterpart_plan(
    "counterpart.web.style.v1",
    "web.resolve.computed_style@1",
    "web-pinned-deterministic",
    "fixture.html",
    [a_candidate_source(), an_independent_reference()],
    [plan_comparison("chrome", "chrome", CounterpartRelation.canonical_exact)]
)
step("Confirm the self-comparison is refused")
val rejections = counterpart_plan_rejections(plan)
expect(rejections.len()).to_be_greater_than(0)
```

</details>

### Counterpart execution receipts

#### reports every reason a GPU lane failed to prove GPU execution

- reports every reason a GPU lane failed to prove GPU execution
- Present a receipt from a lane that silently fell back to CPU
- Confirm the fallback is named as the failure
   - Expected: failures.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("reports every reason a GPU lane failed to prove GPU execution")
step("Present a receipt from a lane that silently fell back to CPU")
val failures = execution_receipt_gpu_gate_failures(a_gpu_receipt_that_fell_back())
step("Confirm the fallback is named as the failure")
expect(failures.len()).to_equal(1)
expect(failures[0]).to_contain("fallback_used")
```

</details>

#### accepts a receipt that proves submission, fence and device readback

- accepts a receipt that proves submission, fence and device readback
- Present a receipt from a lane that genuinely reached the device
- Confirm the gate raises nothing
   - Expected: failures.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("accepts a receipt that proves submission, fence and device readback")
step("Present a receipt from a lane that genuinely reached the device")
val failures = execution_receipt_gpu_gate_failures(a_healthy_gpu_receipt())
step("Confirm the gate raises nothing")
expect(failures.len()).to_equal(0)
```

</details>

#### refuses a GPU claim that never submitted any work

- refuses a GPU claim that never submitted any work
- Present a receipt whose submission count is zero
- Confirm submission, fence and readback are each reported
   - Expected: failures.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses a GPU claim that never submitted any work")
step("Present a receipt whose submission count is zero")
val receipt = ExecutionReceipt(
    provider_id: "simple-web",
    execution_mode: ExecutionMode.vulkan,
    device_identity: "swiftshader-pinned",
    queue_identity: "gfx0",
    submission_count: 0,
    fence_completed: false,
    device_origin_readback: false,
    fallback_used: false,
    dropped_events: 0,
    completed: true
)
step("Confirm submission, fence and readback are each reported")
val failures = execution_receipt_gpu_gate_failures(receipt)
expect(failures.len()).to_equal(3)
```

</details>

### Counterpart run vacuity

#### accepts a run with two independent sources and a real comparison

- accepts a run with two independent sources and a real comparison
- Assemble a run from two sources in different independence groups
- Confirm the run is not vacuous
   - Expected: counterpart_run_vacuity_failures(run).len() equals `0`
   - Expected: counterpart_run_sources_executed(run) equals `2`
   - Expected: counterpart_run_comparisons_failed(run) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("accepts a run with two independent sources and a real comparison")
step("Assemble a run from two sources in different independence groups")
val run = a_run(
    [
        a_source_result("simple_cpu", "simple-web", ProviderStatus.executed),
        a_source_result("chrome", "blink", ProviderStatus.executed)
    ],
    [a_matched_cell()]
)
step("Confirm the run is not vacuous")
expect(counterpart_run_vacuity_failures(run).len()).to_equal(0)
expect(counterpart_run_sources_executed(run)).to_equal(2)
expect(counterpart_run_comparisons_failed(run)).to_equal(0)
```

</details>

#### refuses a run whose sources all share one independence group

- refuses a run whose sources all share one independence group
- Assemble a run from two wrappers over the same upstream engine
- Confirm the framework counts one reference, not two
   - Expected: counterpart_run_independence_groups(run).len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses a run whose sources all share one independence group")
step("Assemble a run from two wrappers over the same upstream engine")
val run = a_run(
    [
        a_source_result("chrome_a", "blink", ProviderStatus.executed),
        a_source_result("chrome_b", "blink", ProviderStatus.executed)
    ],
    [a_matched_cell()]
)
step("Confirm the framework counts one reference, not two")
expect(counterpart_run_independence_groups(run).len()).to_equal(1)
expect(counterpart_run_vacuity_failures(run).len()).to_be_greater_than(0)
```

</details>

#### refuses to treat an unavailable provider as a pass

- refuses to treat an unavailable provider as a pass
- Assemble a run in which the reference provider never executed
- Confirm the missing provider is reported as a failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses to treat an unavailable provider as a pass")
step("Assemble a run in which the reference provider never executed")
val run = a_run(
    [
        a_source_result("simple_cpu", "simple-web", ProviderStatus.executed),
        a_source_result("chrome", "blink", ProviderStatus.unavailable)
    ],
    [a_matched_cell()]
)
step("Confirm the missing provider is reported as a failure")
val failures = counterpart_run_vacuity_failures(run)
expect(failures.len()).to_be_greater_than(0)
```

</details>

#### refuses a run that compared nothing

- refuses a run that compared nothing
- Assemble a run with executed sources but an empty matrix
- Confirm zero comparisons is a failure, not a clean run


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses a run that compared nothing")
step("Assemble a run with executed sources but an empty matrix")
val run = a_run(
    [
        a_source_result("simple_cpu", "simple-web", ProviderStatus.executed),
        a_source_result("chrome", "blink", ProviderStatus.executed)
    ],
    []
)
step("Confirm zero comparisons is a failure, not a clean run")
val failures = counterpart_run_vacuity_failures(run)
expect(failures.len()).to_be_greater_than(0)
```

</details>

#### refuses an artifact that resolved zero items

- refuses an artifact that resolved zero items
- Present a canonical artifact with no items in it
- Confirm an empty artifact is not evidence of agreement


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses an artifact that resolved zero items")
step("Present a canonical artifact with no items in it")
val empty = logical_artifact(
    "web.resolve.computed_style@1", "canonical_style_table", 1, 0, "aa11", "ref")
step("Confirm an empty artifact is not evidence of agreement")
assert_true(logical_artifact_is_vacuous(empty))
```

</details>

### Counterpart oracle authority and conversion loss

#### ranks a normative vector above any agreeing peers

- ranks a normative vector above any agreeing peers
- Compare the authority of a normative vector and a differential peer
- Confirm consensus cannot outrank the vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("ranks a normative vector above any agreeing peers")
step("Compare the authority of a normative vector and a differential peer")
val vector_rank = oracle_authority_rank(OracleAuthority.normative_vector)
val peer_rank = oracle_authority_rank(OracleAuthority.differential_peer)
step("Confirm consensus cannot outrank the vector")
expect(vector_rank).to_be_greater_than(peer_rank)
```

</details>

#### forbids an exact relation from traversing a semantic projection

- forbids an exact relation from traversing a semantic projection
- Read the loss ceiling an exact relation permits
- Confirm a semantic projection exceeds it


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("forbids an exact relation from traversing a semantic projection")
step("Read the loss ceiling an exact relation permits")
val ceiling = relation_max_permitted_loss_rank(CounterpartRelation.byte_exact)
step("Confirm a semantic projection exceeds it")
assert_true(relation_requires_exactness(CounterpartRelation.byte_exact))
expect(conversion_loss_rank(ConversionLoss.semantic_projection)).to_be_greater_than(ceiling)
```

</details>

#### permits a semantic relation to traverse a semantic projection

- permits a semantic relation to traverse a semantic projection
- Read the loss ceiling a semantic relation permits
- Confirm the projection is within it
   - Expected: conversion_loss_rank(ConversionLoss.semantic_projection) equals `ceiling`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("permits a semantic relation to traverse a semantic projection")
step("Read the loss ceiling a semantic relation permits")
val ceiling = relation_max_permitted_loss_rank(CounterpartRelation.semantic_equal)
step("Confirm the projection is within it")
assert_false(relation_requires_exactness(CounterpartRelation.semantic_equal))
expect(conversion_loss_rank(ConversionLoss.semantic_projection)).to_equal(ceiling)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/infra/counterpart/counterpart_conformance_parallel_agent_plan_2026-08-09.md`
- **Design:** `doc/05_design/infra/counterpart/counterpart_conformance_infrastructure_design_2026-08-09.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INFRA`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c8d2fe26abe882138faadfbfeb3ec4be2ad211effc387740d018553a0b0ed0b6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c8d2fe26abe882138faadfbfeb3ec4be2ad211effc387740d018553a0b0ed0b6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c8d2fe26abe882138faadfbfeb3ec4be2ad211effc387740d018553a0b0ed0b6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/infra/counterpart/contract_model_spec.spl
mirror: doc/06_spec/01_unit/infra/counterpart/contract_model_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/infra/counterpart/contract_model_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/01_unit/infra/counterpart/contract_model_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/infra/counterpart/contract_model_spec.spl:210:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a plan naming a candidate and an independent reference' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/infra/counterpart/contract_model_spec.spl:220:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips a boundary identifier through its text form' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/infra/counterpart/contract_model_spec.spl:239:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses a boundary identifier with no schema version' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
