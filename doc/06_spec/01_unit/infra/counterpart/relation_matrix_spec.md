# Counterpart Relation and N-Way Matrix Engine

> Two artifacts agreeing is not, by itself, evidence. Four things decide whether

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Counterpart Relation and N-Way Matrix Engine

Two artifacts agreeing is not, by itself, evidence. Four things decide whether

## At a Glance

| Field | Value |
|-------|-------|
| Category | Infrastructure |
| Status | In Progress |
| Plan | doc/03_plan/infra/counterpart/counterpart_conformance_parallel_agent_plan_2026-08-09.md |
| Design | doc/05_design/infra/counterpart/counterpart_conformance_infrastructure_design_2026-08-09.md |
| Source | `test/01_unit/infra/counterpart/relation_matrix_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Two artifacts agreeing is not, by itself, evidence. Four things decide whether
an N-way counterpart run means anything: which relation was asked for, how
authoritative each side is, whether the sources were genuinely independent, and
— for a GPU lane — whether the work actually happened on the device.

The audience is an engineer reading a counterpart run and deciding whether to
believe it. This specification pins the cases where a run that *looks* green
must be reported red.

## Scope and Preconditions

The relation engine evaluates one relation between two logical artifacts and
returns a comparison cell carrying a mismatch count and the conversion loss it
was reached through. The matrix engine drives a whole plan and returns a run
whose `rejections` list is the verdict — empty means accepted.

## Primary Workflow

Build a plan naming its sources and their oracle authority, collect one source
result per source, and evaluate. Complex relations such as `cross_decode` and
`round_trip` are evaluated here and projected into counted facts, so the stable
Modern SSpec `OracleMode` enum does not have to grow.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Oracle authority | normative_vector > normative_spec_rule > independent_reference > differential_peer > self_execution_mode > diagnostic_only |
| Independence group | Two wrappers over one upstream engine are ONE reference |
| GPU gate | submission, fence, device-origin readback, no fallback, no dropped events |
| Vacuity | Zero comparisons, zero executed sources, or an empty artifact is a failure |

## Related Specifications

- [Converter graph](converter_graph_spec.spl) — how artifacts reach a shared schema

## Evidence and Provenance

Executable against
`src/lib/nogc_sync_mut/spec/evidence/counterpart/relation_engine.spl` and
`matrix_compare.spl`. The four refusal scenarios at the end are the reason this
file exists.

## Recovery and Troubleshooting

Every rejection is a sentence naming the source and the rule. A GPU rejection
means the lane did not run on the device; do not relax the gate to clear it.

## Compatibility and Limitations

Where a plan carries no projected element sequence, `ordered_equal` and
`multiset_equal` fall back to the canonical hash, which is order-sensitive by
construction. That fallback is stated in the comparison detail.

## Scenarios

### Counterpart relation engine

#### reports agreement for an exact relation over an identity route

- reports agreement for an exact relation over an identity route
- Compare two artifacts with the same canonical hash


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("reports agreement for an exact relation over an identity route")
step("Compare two artifacts with the same canonical hash")
val cell = evaluate_relation(relation_input(
    "simple_cpu", "chrome", CounterpartRelation.byte_exact,
    ConversionLoss.identity, an_artifact("h1", 16), an_artifact("h1", 16)))
assert_true(cell.matched)
assert_equal(cell.mismatch_count, 0)
```

</details>

#### refuses an exact relation reached through a semantic projection

- refuses an exact relation reached through a semantic projection
- Compare two identical artifacts, but across a lossy route
- Confirm identical hashes do NOT rescue an unsound route


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses an exact relation reached through a semantic projection")
step("Compare two identical artifacts, but across a lossy route")
val cell = evaluate_relation(relation_input(
    "simple_cpu", "chrome", CounterpartRelation.byte_exact,
    ConversionLoss.semantic_projection, an_artifact("h1", 16), an_artifact("h1", 16)))
step("Confirm identical hashes do NOT rescue an unsound route")
assert_false(cell.matched)
assert_true(cell.detail.contains("semantic_projection"))
```

</details>

#### refuses a comparison against a vacuous artifact

- refuses a comparison against a vacuous artifact
- Compare a populated artifact against one that resolved zero items


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses a comparison against a vacuous artifact")
step("Compare a populated artifact against one that resolved zero items")
val cell = evaluate_relation(relation_input(
    "simple_cpu", "chrome", CounterpartRelation.canonical_exact,
    ConversionLoss.identity, an_artifact("h1", 16), an_artifact("h1", 0)))
assert_false(cell.matched)
assert_true(cell.detail.contains("vacuous"))
```

</details>

#### separates ordered_equal from multiset_equal

- separates ordered_equal from multiset_equal
- Compare two sequences that are permutations of each other
- Order-sensitively they disagree
- As multisets they agree


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("separates ordered_equal from multiset_equal")
step("Compare two sequences that are permutations of each other")
val base = relation_input(
    "simple_cpu", "chrome", CounterpartRelation.ordered_equal,
    ConversionLoss.canonicalizing, an_artifact("h1", 3), an_artifact("h2", 3))
val ordered = evaluate_relation(
    relation_input_with_elements(base, ["a", "b", "c"], ["c", "b", "a"]))
step("Order-sensitively they disagree")
assert_false(ordered.matched)
step("As multisets they agree")
val as_multiset = relation_input(
    "simple_cpu", "chrome", CounterpartRelation.multiset_equal,
    ConversionLoss.canonicalizing, an_artifact("h1", 3), an_artifact("h2", 3))
val multiset = evaluate_relation(
    relation_input_with_elements(as_multiset, ["a", "b", "c"], ["c", "b", "a"]))
assert_true(multiset.matched)
```

</details>

#### refuses a numeric tolerance that carries no reason

- refuses a numeric tolerance that carries no reason
- Compare two metrics within a tolerance that was never justified
- State the reason, and the same comparison is admissible


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses a numeric tolerance that carries no reason")
step("Compare two metrics within a tolerance that was never justified")
val base = relation_input(
    "simple_cpu", "chrome", CounterpartRelation.numeric_bound,
    ConversionLoss.canonicalizing, an_artifact("h1", 16), an_artifact("h2", 16))
val unjustified = evaluate_relation(base)
assert_false(unjustified.matched)
assert_true(unjustified.detail.contains("tolerance reason"))
step("State the reason, and the same comparison is admissible")
val justified = evaluate_relation(relation_input_with_tolerance(
    base, 2, "IEEE-754 rounding across two rasterizers, CSSOM 6.1"))
assert_true(justified.matched)
```

</details>

#### counts cross_decode cases and projects them as facts

- counts cross_decode cases and projects them as facts
- Report sixteen executed cross-decode cases with no failures
- Confirm the counts are projected, not folded into an oracle mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("counts cross_decode cases and projects them as facts")
step("Report sixteen executed cross-decode cases with no failures")
val base = relation_input(
    "simple_cpu", "chrome", CounterpartRelation.cross_decode,
    ConversionLoss.canonicalizing, an_artifact("h1", 16), an_artifact("h2", 16))
val input = relation_input_with_facts(base, relation_facts(16, 0))
val cell = evaluate_relation(input)
assert_true(cell.matched)
step("Confirm the counts are projected, not folded into an oracle mode")
val facts = relation_projected_facts(input, cell)
assert_equal(facts[0], "counterpart.cross_decode.executed=16")
assert_equal(facts[1], "counterpart.cross_decode.failed=0")
```

</details>

#### refuses a round_trip that executed nothing

- refuses a round_trip that executed nothing
- Report zero executed round-trip cases and zero failures
- Confirm 'nothing failed' is not reported as agreement


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses a round_trip that executed nothing")
step("Report zero executed round-trip cases and zero failures")
val base = relation_input(
    "simple_cpu", "chrome", CounterpartRelation.round_trip,
    ConversionLoss.canonicalizing, an_artifact("h1", 16), an_artifact("h2", 16))
val cell = evaluate_relation(relation_input_with_facts(base, relation_facts(0, 0)))
step("Confirm 'nothing failed' is not reported as agreement")
assert_false(cell.matched)
assert_true(cell.detail.contains("executed=0"))
```

</details>

### Counterpart N-way matrix

#### accepts a run whose independent sources agree

- accepts a run whose independent sources agree
- Run two independent sources over one comparison


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("accepts a run whose independent sources agree")
step("Run two independent sources over one comparison")
val plan = a_plan([plan_comparison("simple_cpu", "chrome", CounterpartRelation.canonical_exact)])
val run = evaluate_matrix(plan, [
    a_source("simple_cpu", "simple", "h1", execution_receipt_cpu("p_simple")),
    a_source("chrome", "chromium", "h1", execution_receipt_cpu("p_chrome"))
])
assert_true(matrix_run_accepted(run))
assert_equal(run.matrix.len(), 1)
assert_equal(matrix_independent_group_count(run.sources), 2)
```

</details>

#### fails a run whose sources disagree

- fails a run whose sources disagree
- Give the two sources different canonical hashes


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("fails a run whose sources disagree")
step("Give the two sources different canonical hashes")
val plan = a_plan([plan_comparison("simple_cpu", "chrome", CounterpartRelation.canonical_exact)])
val run = evaluate_matrix(plan, [
    a_source("simple_cpu", "simple", "h1", execution_receipt_cpu("p_simple")),
    a_source("chrome", "chromium", "h2", execution_receipt_cpu("p_chrome"))
])
assert_false(matrix_run_accepted(run))
```

</details>

#### fails a run whose provider never executed

- fails a run whose provider never executed
- Mark one source unavailable
- Confirm an unavailable provider is never a pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("fails a run whose provider never executed")
step("Mark one source unavailable")
val plan = a_plan([plan_comparison("simple_cpu", "chrome", CounterpartRelation.canonical_exact)])
var absent = a_source("chrome", "chromium", "h1", execution_receipt_cpu("p_chrome"))
absent = SourceResult(
    source_id: absent.source_id,
    provider_id: absent.provider_id,
    independence_group: absent.independence_group,
    status: ProviderStatus.unavailable,
    artifact: absent.artifact,
    execution: absent.execution,
    provenance: absent.provenance,
    conversions: absent.conversions,
    diagnostics: absent.diagnostics
)
val run = evaluate_matrix(plan, [
    a_source("simple_cpu", "simple", "h1", execution_receipt_cpu("p_simple")),
    absent
])
step("Confirm an unavailable provider is never a pass")
assert_false(matrix_run_accepted(run))
assert_equal(run.matrix.len(), 1)
assert_false(run.matrix[0].matched)
```

</details>

### Counterpart matrix measures the converter route it traversed

#### carries the measured route loss into the comparison cell

- carries the measured route loss into the comparison cell
- Register a semantic_projection converter between two schemas
- Compare a chrome-schema source against a canonical-schema source
- Confirm the cell reports the loss it actually traversed


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("carries the measured route loss into the comparison cell")
step("Register a semantic_projection converter between two schemas")
val registry = registry_register(converter_registry(), converter_manifest(
    "project", "1.0.0", "chrome.dom@1", "canonical.node_arena@1",
    ConversionLoss.semantic_projection))
step("Compare a chrome-schema source against a canonical-schema source")
val plan = a_plan([plan_comparison("simple_cpu", "chrome", CounterpartRelation.semantic_equal)])
val run = evaluate_matrix_with_registry(plan, [
    a_source_at("simple_cpu", "simple", "h1", "chrome.dom"),
    a_source_at("chrome", "chromium", "h1", "canonical.node_arena")
], registry)
step("Confirm the cell reports the loss it actually traversed")
assert_equal(conversion_loss_name(run.matrix[0].route_loss), "semantic_projection")
```

</details>

#### reports a measured identity route when both sources share a schema

- reports a measured identity route when both sources share a schema
- Compare two sources already at the canonical schema


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("reports a measured identity route when both sources share a schema")
step("Compare two sources already at the canonical schema")
val plan = a_plan([plan_comparison("simple_cpu", "chrome", CounterpartRelation.byte_exact)])
val run = evaluate_matrix(plan, [
    a_source("simple_cpu", "simple", "h1", execution_receipt_cpu("p_simple")),
    a_source("chrome", "chromium", "h1", execution_receipt_cpu("p_chrome"))
])
assert_equal(conversion_loss_name(run.matrix[0].route_loss), "identity")
assert_true(matrix_run_accepted(run))
```

</details>

#### refuses an exact relation whose sources are only reachable lossily

- refuses an exact relation whose sources are only reachable lossily
- Register the same semantic_projection converter
- Ask for byte_exact across it
- Confirm the matrix itself names the exactness refusal


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses an exact relation whose sources are only reachable lossily")
step("Register the same semantic_projection converter")
val registry = registry_register(converter_registry(), converter_manifest(
    "project", "1.0.0", "chrome.dom@1", "canonical.node_arena@1",
    ConversionLoss.semantic_projection))
step("Ask for byte_exact across it")
val plan = a_plan([plan_comparison("simple_cpu", "chrome", CounterpartRelation.byte_exact)])
val run = evaluate_matrix_with_registry(plan, [
    a_source_at("simple_cpu", "simple", "h1", "chrome.dom"),
    a_source_at("chrome", "chromium", "h1", "canonical.node_arena")
], registry)
step("Confirm the matrix itself names the exactness refusal")
assert_false(matrix_run_accepted(run))
assert_true(run.matrix[0].detail.contains("exact_relation_through_lossy_route"))
```

</details>

#### refuses a comparison across schemas with no declared converter at all

- refuses a comparison across schemas with no declared converter at all
- Compare two differing schemas with an empty converter graph
- Confirm an undeclared conversion is a refusal, not an implicit identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses a comparison across schemas with no declared converter at all")
step("Compare two differing schemas with an empty converter graph")
val plan = a_plan([plan_comparison("simple_cpu", "chrome", CounterpartRelation.semantic_equal)])
val run = evaluate_matrix(plan, [
    a_source_at("simple_cpu", "simple", "h1", "chrome.dom"),
    a_source_at("chrome", "chromium", "h1", "canonical.node_arena")
])
step("Confirm an undeclared conversion is a refusal, not an implicit identity")
assert_false(matrix_run_accepted(run))
assert_true(run.matrix[0].detail.contains("no_route"))
```

</details>

### Counterpart matrix refuses vacuous and unsound runs

#### fails a run that performed zero comparisons

- fails a run that performed zero comparisons
- Declare a plan with no comparisons at all
- Confirm zero comparisons is a rejection


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("fails a run that performed zero comparisons")
step("Declare a plan with no comparisons at all")
val plan = a_plan([])
val run = evaluate_matrix(plan, [
    a_source("simple_cpu", "simple", "h1", execution_receipt_cpu("p_simple")),
    a_source("chrome", "chromium", "h1", execution_receipt_cpu("p_chrome"))
])
step("Confirm zero comparisons is a rejection")
assert_equal(run.matrix.len(), 0)
assert_false(matrix_run_accepted(run))
assert_true(matrix_run_has_rejection_containing(run, "zero comparisons"))
```

</details>

#### does not count two sources in one independence group as independent

- does not count two sources in one independence group as independent
- Give both sources the same independence_group
- Confirm they count as one reference, and the run is refused


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("does not count two sources in one independence group as independent")
step("Give both sources the same independence_group")
val plan = a_plan([plan_comparison("simple_cpu", "chrome", CounterpartRelation.canonical_exact)])
val run = evaluate_matrix(plan, [
    a_source("simple_cpu", "blink_derived", "h1", execution_receipt_cpu("p_simple")),
    a_source("chrome", "blink_derived", "h1", execution_receipt_cpu("p_chrome"))
])
step("Confirm they count as one reference, and the run is refused")
assert_equal(matrix_independent_group_count(run.sources), 1)
assert_false(matrix_run_accepted(run))
assert_true(matrix_run_has_rejection_containing(run, "independent reference"))
```

</details>

#### does not let peer consensus override a disagreeing normative vector

- does not let peer consensus override a disagreeing normative vector
- Two differential peers agree with each other on h1
- The normative vector says h_ref
- Confirm the peers did reach consensus
- Confirm consensus did NOT rescue the run


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("does not let peer consensus override a disagreeing normative vector")
step("Two differential peers agree with each other on h1")
val plan = CounterpartPlan(
    plan_id: "plan-consensus",
    boundary_id: BOUNDARY,
    environment_profile: "linux-x86_64",
    input_ref: "fixture://case-1",
    sources: [
        plan_source("peer_a", "p_a", "resolve", OracleAuthority.differential_peer, true),
        plan_source("peer_b", "p_b", "resolve", OracleAuthority.differential_peer, true),
        plan_source("vector", "p_v", "resolve", OracleAuthority.normative_vector, true)
    ],
    comparisons: [
        plan_comparison("peer_a", "peer_b", CounterpartRelation.canonical_exact),
        plan_comparison("peer_a", "vector", CounterpartRelation.canonical_exact)
    ],
    require_gpu_receipt_source_ids: []
)
step("The normative vector says h_ref")
val run = evaluate_matrix(plan, [
    a_source("peer_a", "grp_a", "h1", execution_receipt_cpu("p_a")),
    a_source("peer_b", "grp_b", "h1", execution_receipt_cpu("p_b")),
    a_source("vector", "grp_v", "h_ref", execution_receipt_cpu("p_v"))
])
step("Confirm the peers did reach consensus")
assert_true(matrix_peer_consensus_matched(plan, run.matrix))
step("Confirm consensus did NOT rescue the run")
assert_false(matrix_run_accepted(run))
assert_true(matrix_run_has_rejection_containing(run, "normative source vector"))
```

</details>

#### fails a GPU-gated source whose receipt admits a CPU fallback

- fails a GPU-gated source whose receipt admits a CPU fallback
- Gate one source on a GPU receipt
- The gated source reports fallback_used=true but a perfect artifact
- Confirm the artifacts agreed, so only the receipt can fail this run


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("fails a GPU-gated source whose receipt admits a CPU fallback")
step("Gate one source on a GPU receipt")
var plan = a_plan([plan_comparison("simple_cpu", "chrome", CounterpartRelation.canonical_exact)])
plan = CounterpartPlan(
    plan_id: plan.plan_id,
    boundary_id: plan.boundary_id,
    environment_profile: plan.environment_profile,
    input_ref: plan.input_ref,
    sources: plan.sources,
    comparisons: plan.comparisons,
    require_gpu_receipt_source_ids: ["simple_cpu"]
)
step("The gated source reports fallback_used=true but a perfect artifact")
val run = evaluate_matrix(plan, [
    a_source("simple_cpu", "simple", "h1", a_gpu_receipt("p_simple", true)),
    a_source("chrome", "chromium", "h1", execution_receipt_cpu("p_chrome"))
])
step("Confirm the artifacts agreed, so only the receipt can fail this run")
assert_true(run.matrix[0].matched)
assert_false(matrix_run_accepted(run))
assert_true(matrix_run_has_rejection_containing(run, "fallback_used=true"))
```

</details>

#### accepts the same GPU-gated source once the fallback is gone

- accepts the same GPU-gated source once the fallback is gone
- Flip fallback_used to false, leaving everything else identical


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("accepts the same GPU-gated source once the fallback is gone")
step("Flip fallback_used to false, leaving everything else identical")
var plan = a_plan([plan_comparison("simple_cpu", "chrome", CounterpartRelation.canonical_exact)])
plan = CounterpartPlan(
    plan_id: plan.plan_id,
    boundary_id: plan.boundary_id,
    environment_profile: plan.environment_profile,
    input_ref: plan.input_ref,
    sources: plan.sources,
    comparisons: plan.comparisons,
    require_gpu_receipt_source_ids: ["simple_cpu"]
)
val run = evaluate_matrix(plan, [
    a_source("simple_cpu", "simple", "h1", a_gpu_receipt("p_simple", false)),
    a_source("chrome", "chromium", "h1", execution_receipt_cpu("p_chrome"))
])
assert_true(matrix_run_accepted(run))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
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

- `REQ-SSPEC-UNIT`
- `REQ-COUNTERPART-F6-001`
- `REQ-SSPEC-INFRA`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ceecfa6d5a01265337429676743ba43533b2a9bc1c4b555276fa82d3d0dfd6c1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ceecfa6d5a01265337429676743ba43533b2a9bc1c4b555276fa82d3d0dfd6c1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ceecfa6d5a01265337429676743ba43533b2a9bc1c4b555276fa82d3d0dfd6c1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/infra/counterpart/relation_matrix_spec.spl
mirror: doc/06_spec/01_unit/infra/counterpart/relation_matrix_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=88; blocker cap makes effective=49
doc/06_spec/01_unit/infra/counterpart/relation_matrix_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/01_unit/infra/counterpart/relation_matrix_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/infra/counterpart/relation_matrix_spec.spl:206:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports agreement for an exact relation over an identity route' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/infra/counterpart/relation_matrix_spec.spl:216:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses an exact relation reached through a semantic projection' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/infra/counterpart/relation_matrix_spec.spl:227:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses a comparison against a vacuous artifact' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
