# layout_cpu_reference_oracle_spec

> Verifies the layout cpu reference oracle behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# layout_cpu_reference_oracle_spec

Verifies the layout cpu reference oracle behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/structural/layout/layout_cpu_reference_oracle_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the layout cpu reference oracle behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### layout CPU reference oracle

#### should produce an empty converged snapshot for an empty input

- Verify: should produce an empty converged snapshot for an empty input
   - Expected: snapshot.fault equals ``
   - Expected: snapshot.contract_version equals `LAYOUT_CONTRACT_VERSION`
   - Expected: snapshot.boxes.len() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: snapshot.fragments.len() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: snapshot.islands.len() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: snapshot.visited_island_ids.len() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: snapshot.receipt.item_count_in equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: snapshot.receipt.item_count_out equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-004 REQ-005 REQ-007
step("Verify: should produce an empty converged snapshot for an empty input")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val input = layout_input(
    [],
    [],
    [],
    oracle_execution("cpu_reference"),
    4
)
val snapshot = layout_run_full(input, layout_text_measure_port_unavailable())

expect(snapshot.fault).to_equal("")
expect(snapshot.contract_version).to_equal(LAYOUT_CONTRACT_VERSION)
expect(snapshot.boxes.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(snapshot.fragments.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(snapshot.islands.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(snapshot.visited_island_ids.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(snapshot.receipt.item_count_in).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(snapshot.receipt.item_count_out).to_equal(0)  # oracle: pinned constant asserted by this scenario
assert_true(snapshot.receipt.converged)
```

</details>

#### should match the CPU oracle geometry for every profile fixture

- Verify: should match the CPU oracle geometry for every profile fixture
   - Expected: snapshot.fault equals ``
   - Expected: snapshot.backend equals `serial_cpu`
   - Expected: snapshot.boxes equals `expected`
   - Expected: snapshot.islands.len() equals `nodes.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-004 REQ-005 REQ-007
step("Verify: should match the CPU oracle geometry for every profile fixture")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val nodes = profile_fixture_nodes()
val expected = oracle_boxes_for(nodes)
val snapshot = layout_run_full(
    cpu_input(nodes, [], [], 4, []),
    layout_text_measure_port_unavailable()
)

expect(snapshot.fault).to_equal("")
expect(snapshot.backend).to_equal("serial_cpu")
expect(snapshot.boxes).to_equal(expected)
expect(snapshot.islands.len()).to_equal(nodes.len())
assert_true(snapshot.execution_proof.executed)
assert_true(snapshot.execution_proof.oracle_verified)
assert_true(snapshot.receipt.oracle_verified)
```

</details>

#### should emit one principal fragment and overflow per laid-out box

- Verify: should emit one principal fragment and overflow per laid-out box
   - Expected: snapshot.fragments.len() equals `nodes.len()`
   - Expected: snapshot.overflows.len() equals `nodes.len()`
   - Expected: snapshot.fragments[0].node_id equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: snapshot.fragments[0].box equals `snapshot.boxes[0]`
   - Expected: snapshot.overflows[0].scroll_width equals `snapshot.boxes[0].width`
   - Expected: snapshot.overflows[0].scroll_height equals `snapshot.boxes[0].height`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-004 REQ-005 REQ-007
step("Verify: should emit one principal fragment and overflow per laid-out box")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val nodes = profile_fixture_nodes()
val snapshot = layout_run_full(
    cpu_input(nodes, [], [], 4, []),
    layout_text_measure_port_unavailable()
)

expect(snapshot.fragments.len()).to_equal(nodes.len())
expect(snapshot.overflows.len()).to_equal(nodes.len())
expect(snapshot.fragments[0].node_id).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(snapshot.fragments[0].box).to_equal(snapshot.boxes[0])
expect(snapshot.overflows[0].scroll_width).to_equal(snapshot.boxes[0].width)
expect(snapshot.overflows[0].scroll_height).to_equal(snapshot.boxes[0].height)
```

</details>

#### should be deterministic across repeated identical runs

- Verify: should be deterministic across repeated identical runs
   - Expected: first.boxes equals `second.boxes`
   - Expected: first.receipt.deterministic_hash equals `second.receipt.deterministic_hash`
   - Expected: first.receipt.output_hash equals `second.receipt.output_hash`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-004 REQ-005 REQ-007
step("Verify: should be deterministic across repeated identical runs")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val nodes = profile_fixture_nodes()
val input = cpu_input(nodes, [], [], 4, [])
val first = layout_run_full(input, layout_text_measure_port_unavailable())
val second = layout_run_full(input, layout_text_measure_port_unavailable())

expect(first.boxes).to_equal(second.boxes)
expect(first.receipt.deterministic_hash).to_equal(second.receipt.deterministic_hash)
expect(first.receipt.output_hash).to_equal(second.receipt.output_hash)
```

</details>

#### should yield identical geometry from incremental and full layout

- Verify: should yield identical geometry from incremental and full layout
   - Expected: incremental.fault equals ``
   - Expected: incremental.boxes equals `full.boxes`
   - Expected: incremental.receipt.output_hash equals `full.receipt.output_hash`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-004 REQ-005 REQ-007
step("Verify: should yield identical geometry from incremental and full layout")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val nodes = profile_fixture_nodes()
val full = layout_run_full(
    cpu_input(nodes, [], [], 4, []),
    layout_text_measure_port_unavailable()
)
val incremental = layout_run_incremental(
    cpu_input(nodes, [], [4], 4, full.boxes),
    layout_text_measure_port_unavailable()
)

expect(incremental.fault).to_equal("")
expect(incremental.boxes).to_equal(full.boxes)
expect(incremental.receipt.output_hash).to_equal(full.receipt.output_hash)
```

</details>

#### should visit only the invalidated island during incremental layout

- Verify: should visit only the invalidated island during incremental layout
   - Expected: full.receipt.visited_island_ids.len() equals `nodes.len()`
   - Expected: incremental.receipt.visited_island_ids equals `[4]`
   - Expected: incremental.receipt.mode equals `incremental`
   - Expected: full.receipt.mode equals `full`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-004 REQ-005 REQ-007
step("Verify: should visit only the invalidated island during incremental layout")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val nodes = profile_fixture_nodes()
val full = layout_run_full(
    cpu_input(nodes, [], [], 4, []),
    layout_text_measure_port_unavailable()
)
val incremental = layout_run_incremental(
    cpu_input(nodes, [], [4], 4, full.boxes),
    layout_text_measure_port_unavailable()
)

expect(full.receipt.visited_island_ids.len()).to_equal(nodes.len())
expect(incremental.receipt.visited_island_ids).to_equal([4])
expect(incremental.receipt.mode).to_equal("incremental")
expect(full.receipt.mode).to_equal("full")
```

</details>

#### should pull dirty producers into the incremental island selection

- Verify: should pull dirty producers into the incremental island selection
   - Expected: incremental.fault equals ``
   - Expected: incremental.receipt.visited_island_ids equals `[1, 4]`
   - Expected: incremental.boxes equals `full.boxes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-004 REQ-005 REQ-007
step("Verify: should pull dirty producers into the incremental island selection")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val nodes = profile_fixture_nodes()
val full = layout_run_full(
    cpu_input(nodes, [], [], 4, []),
    layout_text_measure_port_unavailable()
)
# island 1 produces intrinsic size consumed by island 4, so invalidating
# the consumer must also revisit the producer.
val dependencies = [layout_dependency(1, 4, "intrinsic-size", 1)]
val incremental = layout_run_incremental(
    cpu_input(nodes, dependencies, [4], 4, full.boxes),
    layout_text_measure_port_unavailable()
)

expect(incremental.fault).to_equal("")
expect(incremental.receipt.visited_island_ids).to_equal([1, 4])
expect(incremental.boxes).to_equal(full.boxes)
```

</details>

#### should reject a retained snapshot that does not match the node set

- Verify: should reject a retained snapshot that does not match the node set
   - Expected: snapshot.fault equals `retained-layout-shape-mismatch`
   - Expected: snapshot.receipt.malformed_count equals `1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-004 REQ-005 REQ-007
step("Verify: should reject a retained snapshot that does not match the node set")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val nodes = profile_fixture_nodes()
val stale_retained = [layout_box(1, 0, 0, 10, 10)]
val snapshot = layout_run_incremental(
    cpu_input(nodes, [], [4], 4, stale_retained),
    layout_text_measure_port_unavailable()
)

expect(snapshot.fault).to_equal("retained-layout-shape-mismatch")
expect(snapshot.receipt.malformed_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
assert_false(snapshot.receipt.converged)
```

</details>

#### should reject an oracle whose box identities do not match the nodes

- Verify: should reject an oracle whose box identities do not match the nodes
   - Expected: snapshot.fault equals `oracle-shape-mismatch`
   - Expected: snapshot.receipt.malformed_count equals `1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-004 REQ-005 REQ-007
step("Verify: should reject an oracle whose box identities do not match the nodes")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val nodes = profile_fixture_nodes()
val mismatched = layout_input(
    nodes,
    [],
    [],
    oracle_execution("cpu_reference"),
    4,
    0,
    0,
    [],
    [layout_box(99, 0, 0, 10, 10)]
)
val snapshot = layout_run_full(mismatched, layout_text_measure_port_unavailable())

expect(snapshot.fault).to_equal("oracle-shape-mismatch")
expect(snapshot.receipt.malformed_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### should converge a cyclic island group within the fixed point cap

- Verify: should converge a cyclic island group within the fixed point cap
   - Expected: snapshot.fault equals ``
   - Expected: snapshot.receipt.iterations equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: snapshot.boxes equals `oracle_boxes_for(nodes)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-004 REQ-005 REQ-007
step("Verify: should converge a cyclic island group within the fixed point cap")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val nodes = [
    oracle_node(1, "block", 0),
    oracle_node(2, "block", 0),
    oracle_node(3, "block", 0)
]
val dependencies = [
    layout_dependency(1, 2, "containing-block", 1),
    layout_dependency(2, 3, "percentage", 1),
    layout_dependency(3, 2, "baseline", 1)
]
val snapshot = layout_run_full(
    cpu_input(nodes, dependencies, [], 4, []),
    layout_text_measure_port_unavailable()
)

expect(snapshot.fault).to_equal("")
assert_true(snapshot.receipt.converged)
expect(snapshot.receipt.iterations).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(snapshot.boxes).to_equal(oracle_boxes_for(nodes))
```

</details>

#### should fault explicitly when the fixed point cap is exhausted

- Verify: should fault explicitly when the fixed point cap is exhausted
   - Expected: snapshot.fault equals `non-convergent`
   - Expected: snapshot.receipt.iterations equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: snapshot.receipt.malformed_count equals `1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-004 REQ-005 REQ-007
step("Verify: should fault explicitly when the fixed point cap is exhausted")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val nodes = [
    oracle_node(1, "block", 0),
    oracle_node(2, "block", 0),
    oracle_node(3, "block", 0)
]
val dependencies = [
    layout_dependency(1, 2, "containing-block", 1),
    layout_dependency(2, 3, "percentage", 1),
    layout_dependency(3, 2, "baseline", 1)
]
val snapshot = layout_run_full(
    cpu_input(nodes, dependencies, [], 1, []),
    layout_text_measure_port_unavailable()
)

expect(snapshot.fault).to_equal("non-convergent")
assert_false(snapshot.receipt.converged)
expect(snapshot.receipt.iterations).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(snapshot.receipt.malformed_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### should reject an invalid fixed point cap before executing

- Verify: should reject an invalid fixed point cap before executing
   - Expected: snapshot.fault equals `invalid-fixed-point-cap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-004 REQ-005 REQ-007
step("Verify: should reject an invalid fixed point cap before executing")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val nodes = profile_fixture_nodes()
val snapshot = layout_run_full(
    cpu_input(nodes, [], [], 0, []),
    layout_text_measure_port_unavailable()
)

expect(snapshot.fault).to_equal("invalid-fixed-point-cap")
assert_false(snapshot.execution_proof.executed)
```

</details>

#### should record a reason receipt whenever the CPU backend is selected

- Verify: should record a reason receipt whenever the CPU backend is selected
   - Expected: snapshot.backend equals `serial_cpu`
   - Expected: snapshot.receipt.candidate_backend equals `serial_cpu`
   - Expected: snapshot.receipt.fallback_reason equals `gpu-mode-disabled`
   - Expected: snapshot.execution_proof.reason equals `gpu-mode-disabled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-004 REQ-005 REQ-007
step("Verify: should record a reason receipt whenever the CPU backend is selected")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val nodes = profile_fixture_nodes()
val snapshot = layout_run_full(
    cpu_input(nodes, [], [], 4, []),
    layout_text_measure_port_unavailable()
)

expect(snapshot.backend).to_equal("serial_cpu")
expect(snapshot.receipt.candidate_backend).to_equal("serial_cpu")
expect(snapshot.receipt.fallback_reason).to_equal("gpu-mode-disabled")
expect(snapshot.execution_proof.reason).to_equal("gpu-mode-disabled")
```

</details>

#### should name the reason when a GPU candidate cannot be oracle-checked

- Verify: should name the reason when a GPU candidate cannot be oracle-checked
   - Expected: snapshot.receipt.candidate_backend equals `hybrid_vector_gpu`
   - Expected: snapshot.backend equals `serial_cpu`
   - Expected: snapshot.receipt.fallback_reason equals `gpu-oracle-unavailable`
   - Expected: snapshot.receipt.fallback_count equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: snapshot.fault equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-004 REQ-005 REQ-007
step("Verify: should name the reason when a GPU candidate cannot be oracle-checked")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val nodes = [
    oracle_node(1, "block", 0),
    oracle_node(2, "block", 0)
]
val input = layout_input(
    nodes,
    [],
    [],
    oracle_execution("hybrid_vector_gpu"),
    4
)
val snapshot = layout_run_full(input, layout_text_measure_port_unavailable())

expect(snapshot.receipt.candidate_backend).to_equal("hybrid_vector_gpu")
expect(snapshot.backend).to_equal("serial_cpu")
expect(snapshot.receipt.fallback_reason).to_equal("gpu-oracle-unavailable")
expect(snapshot.receipt.fallback_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(snapshot.fault).to_equal("")
```

</details>

#### should stay on the CPU without device traffic in cpu reference mode

- Verify: should stay on the CPU without device traffic in cpu reference mode
   - Expected: snapshot.receipt.stage equals `layout`
   - Expected: snapshot.receipt.bytes_read equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: snapshot.receipt.bytes_written equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-004 REQ-005 REQ-007
step("Verify: should stay on the CPU without device traffic in cpu reference mode")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val nodes = profile_fixture_nodes()
val snapshot = layout_run_full(
    cpu_input(nodes, [], [], 4, []),
    layout_text_measure_port_unavailable()
)

expect(snapshot.receipt.stage).to_equal("layout")
expect(snapshot.receipt.bytes_read).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(snapshot.receipt.bytes_written).to_equal(0)  # oracle: pinned constant asserted by this scenario
assert_false(snapshot.execution_proof.submitted)
assert_false(snapshot.execution_proof.device_readback)
```

</details>

#### should map every laid-out island into the layout mapping graph

- Verify: should map every laid-out island into the layout mapping graph
   - Expected: snapshot.mappings.len() equals `nodes.len()`
   - Expected: snapshot.island_costs.len() equals `nodes.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-004 REQ-005 REQ-007
step("Verify: should map every laid-out island into the layout mapping graph")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val nodes = profile_fixture_nodes()
val snapshot = layout_run_full(
    cpu_input(nodes, [], [], 4, []),
    layout_text_measure_port_unavailable()
)

expect(snapshot.mappings.len()).to_equal(nodes.len())
expect(snapshot.island_costs.len()).to_equal(nodes.len())
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `26279d373c095eda6bbec9030d822d9675056fa9cbc9bb43b4f3ac5d88921178`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `26279d373c095eda6bbec9030d822d9675056fa9cbc9bb43b4f3ac5d88921178`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `26279d373c095eda6bbec9030d822d9675056fa9cbc9bb43b4f3ac5d88921178`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/structural/layout/layout_cpu_reference_oracle_spec.spl
mirror: doc/06_spec/01_unit/lib/structural/layout/layout_cpu_reference_oracle_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/structural/layout/layout_cpu_reference_oracle_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/lib/structural/layout/layout_cpu_reference_oracle_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/structural/layout/layout_cpu_reference_oracle_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/structural/layout/layout_cpu_reference_oracle_spec.spl:116:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should produce an empty converged snapshot for an empty input' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/structural/layout/layout_cpu_reference_oracle_spec.spl:139:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should match the CPU oracle geometry for every profile fixture' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/structural/layout/layout_cpu_reference_oracle_spec.spl:158:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should emit one principal fragment and overflow per laid-out box' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/structural/layout/layout_cpu_reference_oracle_spec.spl:175:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should be deterministic across repeated identical runs' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/structural/layout/layout_cpu_reference_oracle_spec.spl:188:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should yield identical geometry from incremental and full layout' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/structural/layout/layout_cpu_reference_oracle_spec.spl:206:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should visit only the invalidated island during incremental layout' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
