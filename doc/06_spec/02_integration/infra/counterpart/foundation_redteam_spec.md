# Counterpart Foundation — Adversarial Acceptance-Gate Suite

> Every other counterpart specification demonstrates that the framework accepts a

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Counterpart Foundation — Adversarial Acceptance-Gate Suite

Every other counterpart specification demonstrates that the framework accepts a

## At a Glance

| Field | Value |
|-------|-------|
| Category | Infrastructure |
| Status | In Progress |
| Plan | doc/03_plan/infra/counterpart/counterpart_conformance_parallel_agent_plan_2026-08-09.md |
| Design | doc/05_design/infra/counterpart/counterpart_conformance_infrastructure_design_2026-08-09.md |
| Source | `test/02_integration/infra/counterpart/foundation_redteam_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Every other counterpart specification demonstrates that the framework accepts a
good run. This one exists to demonstrate that it *refuses a bad one*. Each
scenario constructs an input that the design's §16 acceptance-gate table says
must be rejected, and asserts the exact refusal — never merely that "something
went wrong".

The audience is a reviewer deciding whether a green counterpart run means the
implementations agreed, or only that nothing was actually checked.

## Scope and Preconditions

Reachable foundation only: the frozen model, the relation engine, the N-way
matrix engine, the converter graph, the evidence projection, the artifact store,
and the Modern SSpec comparator's vacuity rules. The in-process
`rt_counterpart_*` ABI shim is not linked into the runtime yet
(doc/08_tracking/bug/counterpart_abi_shim_not_linked_into_runtime_2026-08-09.md),
so ABI negotiation, adapter isolation and license/SBOM provenance gates are out
of scope here.

## Primary Workflow

Build the adversarial artifact, run it through the real gate, and assert the
refusal text. A scenario that can only show a happy path proves nothing and is
not written here.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Vacuity | Zero comparisons, zero executed sources, or an empty artifact is a failure, never a pass |
| Unavailable | A provider that could not run is UNAVAILABLE; it may never be absorbed into a pass |
| Exactness | An exact relation may not be reached through a lossy converter |
| Independence | Sources sharing an `independence_group` are ONE reference |
| Authority | Peer consensus never overrides a disagreeing normative vector |
| Derived expectation | A converter may not compute its expected value from the candidate's own output |

## Related Specifications

- [Relation and matrix engine](../../../01_unit/infra/counterpart/relation_matrix_spec.spl)
- [Converter graph](../../../01_unit/infra/counterpart/converter_graph_spec.spl)

## Evidence and Provenance

Every assertion runs against the landed foundation modules. Each guard asserted
here was additionally verified by removing it from the source and confirming
this suite turns red; findings are recorded in
doc/09_report/counterpart_foundation_redteam_2026-08-09.md.

## Recovery and Troubleshooting

A failure here means a gate the design calls non-negotiable is not closed. The
correct response is to close the gate, never to soften the assertion.

## Compatibility and Limitations

The "derived expected value" scenario asserts a rule the design states in §6.3
but that no landed module implements. It is expected RED and is filed as
doc/08_tracking/bug/counterpart_derived_expected_value_gate_absent_2026-08-09.md.

## Scenarios

### Counterpart vacuity gates refuse an empty run

#### refuses a plan that declares zero comparisons

- refuses a plan that declares zero comparisons
- Build a well-formed plan whose comparison list is empty
- Ask the plan validator for its refusal reasons
- Confirm the emptiness itself is named, not merely 'invalid plan'
- Confirm the same plan is refused end to end by the matrix engine


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("refuses a plan that declares zero comparisons")
step("Build a well-formed plan whose comparison list is empty")
val plan = two_source_plan([])
step("Ask the plan validator for its refusal reasons")
val reasons = counterpart_plan_rejections(plan)
step("Confirm the emptiness itself is named, not merely 'invalid plan'")
assert_true(contains_text(reasons, "declares zero comparisons"))
step("Confirm the same plan is refused end to end by the matrix engine")
val run = evaluate_matrix(plan, [
    a_source("simple", "simple", "h1"),
    a_source("chrome", "chromium", "h1")
])
assert_false(matrix_run_accepted(run))
assert_true(matrix_run_has_rejection_containing(run, "zero comparisons"))
```

</details>

#### refuses a run in which no source executed

- refuses a run in which no source executed
- Every source reports UNAVAILABLE while still carrying a full artifact
- Confirm the executed count is zero even though two artifacts exist
- Confirm the vacuity gate names the missing execution
- Confirm evidence projection refuses rather than emitting a clean capture


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("refuses a run in which no source executed")
step("Every source reports UNAVAILABLE while still carrying a full artifact")
val run = a_run([
    a_source_status("simple", "simple", "h1", 16, ProviderStatus.unavailable),
    a_source_status("chrome", "chromium", "h1", 16, ProviderStatus.unavailable)
], [a_matched_cell("simple", "chrome")])
step("Confirm the executed count is zero even though two artifacts exist")
assert_equal(counterpart_run_sources_executed(run), 0)
assert_equal(counterpart_run_sources_unavailable(run), 2)
step("Confirm the vacuity gate names the missing execution")
val failures = counterpart_run_vacuity_failures(run)
assert_true(contains_text(failures, "fewer than two sources executed"))
step("Confirm evidence projection refuses rather than emitting a clean capture")
assert_false(counterpart_run_to_evidence(run).parse_ok)
```

</details>

#### refuses a source whose artifact resolved zero items

- refuses a source whose artifact resolved zero items
- One provider executed but its conversion yielded an empty artifact
- Confirm the empty artifact is named as the reason by BOTH gates


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("refuses a source whose artifact resolved zero items")
step("One provider executed but its conversion yielded an empty artifact")
val empty = a_source_status("chrome", "chromium", "h1", 0, ProviderStatus.executed)
assert_true(logical_artifact_is_vacuous(empty.artifact))
val run = a_run([a_source("simple", "simple", "h1"), empty],
    [a_matched_cell("simple", "chrome")])
step("Confirm the empty artifact is named as the reason by BOTH gates")
assert_true(contains_text(counterpart_run_vacuity_failures(run),
    "produced a vacuous artifact"))
assert_true(contains_text(projection_blockers(run), "produced a vacuous artifact"))
assert_false(counterpart_run_to_evidence(run).parse_ok)
```

</details>

#### refuses a conversion route that resolved zero items

- refuses a conversion route that resolved zero items
- Ask the converter graph for a route over an empty input
- Confirm the graph refuses with the zero-item code, not a silent identity route


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("refuses a conversion route that resolved zero items")
step("Ask the converter graph for a route over an empty input")
val registry = converter_registry()
val resolution = resolve_route(registry,
    route_request("a@1", "a@1", CounterpartRelation.canonical_exact, 0, "hash-in"))
step("Confirm the graph refuses with the zero-item code, not a silent identity route")
assert_false(resolution.resolved)
assert_equal(resolution.rejection_code, "zero_items")
```

</details>

### Counterpart provider absence is reported, never absorbed

#### projects an unavailable provider as a countable fact that fails a zero-unavailable oracle

- projects an unavailable provider as a countable fact that fails a zero-unavailable oracle
- Two providers execute independently; a third is unavailable
- The run projects cleanly — the absence must survive as data, not block the capture
- Apply the design's own oracle: zero providers may be unavailable
- Confirm the oracle FAILS: the missing provider was not silently forgiven


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("projects an unavailable provider as a countable fact that fails a zero-unavailable oracle")
step("Two providers execute independently; a third is unavailable")
val run = a_run([
    a_source("simple", "simple", "h1"),
    a_source("chrome", "chromium", "h1"),
    a_source_status("servo", "servo", "h1", 16, ProviderStatus.unavailable)
], [a_matched_cell("simple", "chrome")])
step("The run projects cleanly — the absence must survive as data, not block the capture")
val evidence = counterpart_run_to_evidence(run)
assert_true(evidence.parse_ok)
step("Apply the design's own oracle: zero providers may be unavailable")
val result = compare_evidence(evidence,
    oracle_spec("counterpart", [
        check_exact("counterpart.providers.unavailable", "0"),
        check_exact("counterpart.providers.executed", "2")
    ]))
step("Confirm the oracle FAILS: the missing provider was not silently forgiven")
assert_equal(evidence_status_is_failed(result.status), true)
```

</details>

#### turns a planned comparison against a missing provider into a failing cell

- turns a planned comparison against a missing provider into a failing cell
- Plan a comparison whose right-hand source crashed
- Confirm the matrix did not shrink: a cell exists and it is unmatched
- Confirm the crash is reported as a crash, not normalised into 'unavailable'


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("turns a planned comparison against a missing provider into a failing cell")
step("Plan a comparison whose right-hand source crashed")
val plan = two_source_plan([
    plan_comparison("simple", "chrome", CounterpartRelation.canonical_exact)
])
val run = evaluate_matrix(plan, [
    a_source("simple", "simple", "h1"),
    a_source_status("chrome", "chromium", "h1", 16, ProviderStatus.crashed)
])
step("Confirm the matrix did not shrink: a cell exists and it is unmatched")
assert_equal(run.matrix.len(), 1)
assert_false(run.matrix[0].matched)
step("Confirm the crash is reported as a crash, not normalised into 'unavailable'")
assert_true(matrix_run_has_rejection_containing(run, "status=crashed"))
assert_false(matrix_run_accepted(run))
```

</details>

### Counterpart routing fails closed

#### refuses an exact relation whose only route is a semantic projection

- refuses an exact relation whose only route is a semantic projection
- Register a single lossy edge between the two schemas
- Request a byte_exact route across it
- Confirm the refusal names exactness, not merely 'no route'


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("refuses an exact relation whose only route is a semantic projection")
step("Register a single lossy edge between the two schemas")
val registry = registry_register_all(converter_registry(), [
    converter_manifest("lossy", "1", "a@1", "b@1", ConversionLoss.semantic_projection)
])
step("Request a byte_exact route across it")
val resolution = resolve_route(registry,
    route_request("a@1", "b@1", CounterpartRelation.byte_exact, 16, "hash-in"))
step("Confirm the refusal names exactness, not merely 'no route'")
assert_false(resolution.resolved)
assert_equal(resolution.rejection_code, "exact_relation_through_lossy_route")
```

</details>

#### refuses a converter that derives its expected value from the candidate output

- refuses a converter that derives its expected value from the candidate output
- Declare a converter that openly states it reads the candidate's own output
- Confirm the registry refuses to admit it (design §6.3, final clause)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("refuses a converter that derives its expected value from the candidate output")
step("Declare a converter that openly states it reads the candidate's own output")
val manifest = converter_manifest_full(
    "peek_candidate", "1", "a@1", "b@1", ConversionLoss.canonicalizing,
    true, [], [], ["derives_expected_from:candidate_output"])
step("Confirm the registry refuses to admit it (design §6.3, final clause)")
val reasons = converter_manifest_rejections(manifest)
assert_true(contains_text(reasons, "candidate_output"))
```

</details>

#### refuses a comparison whose tolerance carries no stated reason

- refuses a comparison whose tolerance carries no stated reason
- Plan a numeric comparison with a bare tolerance of 3
- Confirm the plan validator names the missing rationale
- Confirm the run is refused, so an unexplained tolerance can never widen a pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("refuses a comparison whose tolerance carries no stated reason")
step("Plan a numeric comparison with a bare tolerance of 3")
val plan = two_source_plan([
    plan_comparison_with_tolerance("simple", "chrome",
        CounterpartRelation.numeric_bound, 3, "")
])
step("Confirm the plan validator names the missing rationale")
assert_true(contains_text(counterpart_plan_rejections(plan),
    "declares a tolerance with no reason"))
step("Confirm the run is refused, so an unexplained tolerance can never widen a pass")
val run = evaluate_matrix(plan, [
    a_source("simple", "simple", "h1"),
    a_source("chrome", "chromium", "h1")
])
assert_false(matrix_run_accepted(run))
```

</details>

### Counterpart independence and authority cannot be inflated

#### counts two wrappers over one engine as a single independent reference

- counts two wrappers over one engine as a single independent reference
- Two differently-named sources declare the same independence_group
- Confirm the group count is 1, not 2, despite two provider ids
- Confirm a run built only from them is refused


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("counts two wrappers over one engine as a single independent reference")
step("Two differently-named sources declare the same independence_group")
val results = [
    a_source("chrome_cdp", "chromium", "h1"),
    a_source("chrome_headless", "chromium", "h1")
]
step("Confirm the group count is 1, not 2, despite two provider ids")
assert_equal(matrix_independent_group_count(results), 1)
assert_equal(counterpart_run_independence_groups(a_run(results, [])).len(), 1)
step("Confirm a run built only from them is refused")
val plan = a_plan_with([
    plan_source("chrome_cdp", "p1", "resolve", OracleAuthority.independent_reference, true),
    plan_source("chrome_headless", "p2", "resolve", OracleAuthority.independent_reference, true)
], [plan_comparison("chrome_cdp", "chrome_headless", CounterpartRelation.canonical_exact)])
val run = evaluate_matrix(plan, results)
assert_false(matrix_run_accepted(run))
assert_true(matrix_run_has_rejection_containing(run, "independent reference"))
```

</details>

#### refuses a run where agreeing peers outvote a disagreeing normative vector

- refuses a run where agreeing peers outvote a disagreeing normative vector
- Two differential peers agree with each other; a normative vector disagrees
- Confirm peer consensus is complete — this is the tempting green signal
- Confirm the run is nevertheless refused and the normative source is named


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("refuses a run where agreeing peers outvote a disagreeing normative vector")
step("Two differential peers agree with each other; a normative vector disagrees")
val plan = a_plan_with([
    plan_source("peer_a", "pa", "resolve", OracleAuthority.differential_peer, true),
    plan_source("peer_b", "pb", "resolve", OracleAuthority.differential_peer, true),
    plan_source("vector", "pv", "resolve", OracleAuthority.normative_vector, true)
], [
    plan_comparison("peer_a", "peer_b", CounterpartRelation.canonical_exact),
    plan_comparison("peer_a", "vector", CounterpartRelation.canonical_exact)
])
val run = evaluate_matrix(plan, [
    a_source("peer_a", "impl_a", "agreed"),
    a_source("peer_b", "impl_b", "agreed"),
    a_source("vector", "kat", "authoritative")
])
step("Confirm peer consensus is complete — this is the tempting green signal")
assert_true(matrix_peer_consensus_matched(plan, run.matrix))
step("Confirm the run is nevertheless refused and the normative source is named")
assert_false(matrix_run_accepted(run))
assert_true(matrix_run_has_rejection_containing(run, "normative source vector"))
```

</details>

### Counterpart GPU gate refuses an unproven device run

#### refuses a receipt with no completed fence

- refuses a receipt with no completed fence
- A GPU receipt that submitted work but never waited on a fence


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("refuses a receipt with no completed fence")
step("A GPU receipt that submitted work but never waited on a fence")
val reasons = execution_receipt_gpu_gate_failures(a_gpu_receipt(false, true, 0, 4))
assert_true(contains_text(reasons, "fence_completed=false"))
```

</details>

#### refuses a receipt whose readback did not originate on the device

- refuses a receipt whose readback did not originate on the device
- A GPU receipt whose final readback was synthesized on the CPU


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("refuses a receipt whose readback did not originate on the device")
step("A GPU receipt whose final readback was synthesized on the CPU")
val reasons = execution_receipt_gpu_gate_failures(a_gpu_receipt(true, false, 0, 4))
assert_true(contains_text(reasons, "device_origin_readback=false"))
```

</details>

#### refuses a receipt that dropped events

- refuses a receipt that dropped events
- A GPU receipt that lost two events during capture


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("refuses a receipt that dropped events")
step("A GPU receipt that lost two events during capture")
val reasons = execution_receipt_gpu_gate_failures(a_gpu_receipt(true, true, 2, 4))
assert_true(contains_text(reasons, "dropped_events=2"))
```

</details>

#### refuses a receipt that submitted no work at all

- refuses a receipt that submitted no work at all
- A GPU-mode receipt with zero submissions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("refuses a receipt that submitted no work at all")
step("A GPU-mode receipt with zero submissions")
val reasons = execution_receipt_gpu_gate_failures(a_gpu_receipt(true, true, 0, 0))
assert_true(contains_text(reasons, "submission_count=0"))
```

</details>

#### accepts only a receipt that satisfies every clause

- accepts only a receipt that satisfies every clause
- Flip every sabotaged field back and confirm the gate goes quiet


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("accepts only a receipt that satisfies every clause")
step("Flip every sabotaged field back and confirm the gate goes quiet")
assert_equal(execution_receipt_gpu_gate_failures(a_gpu_receipt(true, true, 0, 4)).len(), 0)
```

</details>

### Counterpart artifact store refuses a fabricated hash

#### refuses a reference that is not a digest at all

- refuses a reference that is not a digest at all
- Ask the store for an invented reference


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("refuses a reference that is not a digest at all")
step("Ask the store for an invented reference")
val outcome = artifact_get("not-a-hash")
assert_false(outcome.ok)
assert_true(outcome.error.contains("not a sha256 ref"))
assert_false(is_sha256_ref("not-a-hash"))
```

</details>

#### refuses a well-formed but fabricated digest that names no stored blob

- refuses a well-formed but fabricated digest that names no stored blob
- Ask for a syntactically perfect sha256 that was never stored


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("refuses a well-formed but fabricated digest that names no stored blob")
step("Ask for a syntactically perfect sha256 that was never stored")
val fabricated = "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
assert_true(is_sha256_ref(fabricated))
val outcome = artifact_get(fabricated)
assert_false(outcome.ok)
assert_true(outcome.error.contains("not in the store"))
```

</details>

#### detects a manifest row whose recorded hash does not match its blob

- detects a manifest row whose recorded hash does not match its blob
- Store real content and read back its true digest
- Round-trip the honest reference to prove the store works at all
- Forge a manifest row that keeps the real path but swaps the hash
- Confirm the verification sweep reports the mismatch instead of trusting the row


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("detects a manifest row whose recorded hash does not match its blob")
step("Store real content and read back its true digest")
val put = artifact_put("counterpart redteam fixture\n", "run-redteam")
assert_true(put.ok)
step("Round-trip the honest reference to prove the store works at all")
assert_true(artifact_get(put.artifact.sha256).ok)
step("Forge a manifest row that keeps the real path but swaps the hash")
val forged = artifact_record(
    ArtifactRef(
        sha256: "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
        path: put.artifact.path,
        byte_len: put.artifact.byte_len
    ),
    "run-redteam", BOUNDARY, "scratch")
step("Confirm the verification sweep reports the mismatch instead of trusting the row")
assert_true(contains_text(artifact_manifest_unverifiable([forged]),
    "content mismatch"))
```

</details>

### Counterpart evidence refuses a vacuous oracle

#### refuses an ignore that states no reason

- refuses an ignore that states no reason
- Project a healthy run so only the oracle can be at fault
- Ignore a node without saying why, alongside a real positive check
- Confirm the whole comparison fails on the unexplained ignore


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("refuses an ignore that states no reason")
step("Project a healthy run so only the oracle can be at fault")
val evidence = counterpart_run_to_evidence(a_run([
    a_source("simple", "simple", "h1"),
    a_source("chrome", "chromium", "h1")
], [a_matched_cell("simple", "chrome")]))
assert_true(evidence.parse_ok)
step("Ignore a node without saying why, alongside a real positive check")
val result = compare_evidence(evidence, oracle_spec("counterpart", [
    check_exact("counterpart.comparisons.failed", "0"),
    check_ignore("counterpart.plan.id", "")
]))
step("Confirm the whole comparison fails on the unexplained ignore")
assert_equal(evidence_status_is_failed(result.status), true)
assert_true(result.summary.contains("no recorded reason"))
```

</details>

#### refuses an oracle that only ignores

- refuses an oracle that only ignores
- Every check is an ignore, each with an honest reason
- Confirm the all-ignore oracle is refused for asserting nothing


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("refuses an oracle that only ignores")
step("Every check is an ignore, each with an honest reason")
val evidence = counterpart_run_to_evidence(a_run([
    a_source("simple", "simple", "h1"),
    a_source("chrome", "chromium", "h1")
], [a_matched_cell("simple", "chrome")]))
val result = compare_evidence(evidence, oracle_spec("counterpart", [
    check_ignore("counterpart.plan.id", "plan ids are run-scoped"),
    check_ignore("counterpart.boundary.id", "boundary is fixed by the plan")
]))
step("Confirm the all-ignore oracle is refused for asserting nothing")
assert_equal(evidence_status_is_failed(result.status), true)
assert_true(result.summary.contains("no positive production check"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
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

- `REQ-SSPEC-INTEGRATION`
- `REQ-COUNTERPART-F9-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bd562a61292992c181ddc86925c0043e47b19651cb7eae39d7a5d837f7ced9f2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bd562a61292992c181ddc86925c0043e47b19651cb7eae39d7a5d837f7ced9f2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bd562a61292992c181ddc86925c0043e47b19651cb7eae39d7a5d837f7ced9f2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/02_integration/infra/counterpart/foundation_redteam_spec.spl
mirror: doc/06_spec/02_integration/infra/counterpart/foundation_redteam_spec.md (current)
findings: 4 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=100
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=89; blocker cap makes effective=49
test/02_integration/infra/counterpart/foundation_redteam_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/02_integration/infra/counterpart/foundation_redteam_spec.spl:263:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses a plan that declares zero comparisons' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/infra/counterpart/foundation_redteam_spec.spl:311:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses a conversion route that resolved zero items' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/infra/counterpart/foundation_redteam_spec.spl:351:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'turns a planned comparison against a missing provider into a failing cell' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
