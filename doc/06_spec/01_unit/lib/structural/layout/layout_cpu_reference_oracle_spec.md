# layout_cpu_reference_oracle_spec

> Operator-facing oracle contract for the spatial layout CPU reference lane.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# layout_cpu_reference_oracle_spec

Operator-facing oracle contract for the spatial layout CPU reference lane.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/structural/layout/layout_cpu_reference_oracle_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Operator-facing oracle contract for the spatial layout CPU reference lane.

    Audience: layout-kernel authors and GPU-port engineers who must prove their
    backend matches the serial CPU oracle byte-for-byte before it can ship.
    Scope: the `layout_run_full` / `layout_run_incremental` execution path —
    geometry parity, incremental island selection, bounded fixed points, and
    honest backend-selection receipts. Out of scope: contract shapes and wave
    scheduling (owned by `layout_framework_spec.spl`).

## Scenarios

### layout CPU reference oracle

#### should produce an empty converged snapshot for an empty input

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should produce an empty converged snapshot for an empty input
   - Expected: snapshot.fault equals ``
   - Expected: snapshot.contract_version equals `LAYOUT_CONTRACT_VERSION`
   - Expected: snapshot.boxes.len() equals `0`
   - Expected: snapshot.fragments.len() equals `0`
   - Expected: snapshot.islands.len() equals `0`
   - Expected: snapshot.visited_island_ids.len() equals `0`
   - Expected: snapshot.receipt.item_count_in equals `0`
   - Expected: snapshot.receipt.item_count_out equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should produce an empty converged snapshot for an empty input")
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
expect(snapshot.boxes.len()).to_equal(0)
expect(snapshot.fragments.len()).to_equal(0)
expect(snapshot.islands.len()).to_equal(0)
expect(snapshot.visited_island_ids.len()).to_equal(0)
expect(snapshot.receipt.item_count_in).to_equal(0)
expect(snapshot.receipt.item_count_out).to_equal(0)
assert_true(snapshot.receipt.converged)
```

</details>

#### should match the CPU oracle geometry for every profile fixture

- should match the CPU oracle geometry for every profile fixture
   - Expected: snapshot.fault equals ``
   - Expected: snapshot.backend equals `serial_cpu`
   - Expected: snapshot.boxes equals `expected`
   - Expected: snapshot.islands.len() equals `nodes.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should match the CPU oracle geometry for every profile fixture")
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

- should emit one principal fragment and overflow per laid-out box
   - Expected: snapshot.fragments.len() equals `nodes.len()`
   - Expected: snapshot.overflows.len() equals `nodes.len()`
   - Expected: snapshot.fragments[0].node_id equals `1`
   - Expected: snapshot.fragments[0].box equals `snapshot.boxes[0]`
   - Expected: snapshot.overflows[0].scroll_width equals `snapshot.boxes[0].width`
   - Expected: snapshot.overflows[0].scroll_height equals `snapshot.boxes[0].height`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should emit one principal fragment and overflow per laid-out box")
val nodes = profile_fixture_nodes()
val snapshot = layout_run_full(
    cpu_input(nodes, [], [], 4, []),
    layout_text_measure_port_unavailable()
)

expect(snapshot.fragments.len()).to_equal(nodes.len())
expect(snapshot.overflows.len()).to_equal(nodes.len())
expect(snapshot.fragments[0].node_id).to_equal(1)
expect(snapshot.fragments[0].box).to_equal(snapshot.boxes[0])
expect(snapshot.overflows[0].scroll_width).to_equal(snapshot.boxes[0].width)
expect(snapshot.overflows[0].scroll_height).to_equal(snapshot.boxes[0].height)
```

</details>

#### should be deterministic across repeated identical runs

- should be deterministic across repeated identical runs
   - Expected: first.boxes equals `second.boxes`
   - Expected: first.receipt.deterministic_hash equals `second.receipt.deterministic_hash`
   - Expected: first.receipt.output_hash equals `second.receipt.output_hash`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should be deterministic across repeated identical runs")
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

- should yield identical geometry from incremental and full layout
   - Expected: incremental.fault equals ``
   - Expected: incremental.boxes equals `full.boxes`
   - Expected: incremental.receipt.output_hash equals `full.receipt.output_hash`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should yield identical geometry from incremental and full layout")
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

- should visit only the invalidated island during incremental layout
   - Expected: full.receipt.visited_island_ids.len() equals `nodes.len()`
   - Expected: incremental.receipt.visited_island_ids equals `[4]`
   - Expected: incremental.receipt.mode equals `incremental`
   - Expected: full.receipt.mode equals `full`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should visit only the invalidated island during incremental layout")
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

- should pull dirty producers into the incremental island selection
   - Expected: incremental.fault equals ``
   - Expected: incremental.receipt.visited_island_ids equals `[1, 4]`
   - Expected: incremental.boxes equals `full.boxes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should pull dirty producers into the incremental island selection")
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

- should reject a retained snapshot that does not match the node set
   - Expected: snapshot.fault equals `retained-layout-shape-mismatch`
   - Expected: snapshot.receipt.malformed_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should reject a retained snapshot that does not match the node set")
val nodes = profile_fixture_nodes()
val stale_retained = [layout_box(1, 0, 0, 10, 10)]
val snapshot = layout_run_incremental(
    cpu_input(nodes, [], [4], 4, stale_retained),
    layout_text_measure_port_unavailable()
)

expect(snapshot.fault).to_equal("retained-layout-shape-mismatch")
expect(snapshot.receipt.malformed_count).to_equal(1)
assert_false(snapshot.receipt.converged)
```

</details>

#### should reject an oracle whose box identities do not match the nodes

- should reject an oracle whose box identities do not match the nodes
   - Expected: snapshot.fault equals `oracle-shape-mismatch`
   - Expected: snapshot.receipt.malformed_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should reject an oracle whose box identities do not match the nodes")
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
expect(snapshot.receipt.malformed_count).to_equal(1)
```

</details>

#### should converge a cyclic island group within the fixed point cap

- should converge a cyclic island group within the fixed point cap
   - Expected: snapshot.fault equals ``
   - Expected: snapshot.receipt.iterations equals `2`
   - Expected: snapshot.boxes equals `oracle_boxes_for(nodes)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should converge a cyclic island group within the fixed point cap")
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
expect(snapshot.receipt.iterations).to_equal(2)
expect(snapshot.boxes).to_equal(oracle_boxes_for(nodes))
```

</details>

#### should fault explicitly when the fixed point cap is exhausted

- should fault explicitly when the fixed point cap is exhausted
   - Expected: snapshot.fault equals `non-convergent`
   - Expected: snapshot.receipt.iterations equals `1`
   - Expected: snapshot.receipt.malformed_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should fault explicitly when the fixed point cap is exhausted")
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
expect(snapshot.receipt.iterations).to_equal(1)
expect(snapshot.receipt.malformed_count).to_equal(1)
```

</details>

#### should reject an invalid fixed point cap before executing

- should reject an invalid fixed point cap before executing
   - Expected: snapshot.fault equals `invalid-fixed-point-cap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should reject an invalid fixed point cap before executing")
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

- should record a reason receipt whenever the CPU backend is selected
   - Expected: snapshot.backend equals `serial_cpu`
   - Expected: snapshot.receipt.candidate_backend equals `serial_cpu`
   - Expected: snapshot.receipt.fallback_reason equals `gpu-mode-disabled`
   - Expected: snapshot.execution_proof.reason equals `gpu-mode-disabled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should record a reason receipt whenever the CPU backend is selected")
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

- should name the reason when a GPU candidate cannot be oracle-checked
   - Expected: snapshot.receipt.candidate_backend equals `hybrid_vector_gpu`
   - Expected: snapshot.backend equals `serial_cpu`
   - Expected: snapshot.receipt.fallback_reason equals `gpu-oracle-unavailable`
   - Expected: snapshot.receipt.fallback_count equals `1`
   - Expected: snapshot.fault equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should name the reason when a GPU candidate cannot be oracle-checked")
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
expect(snapshot.receipt.fallback_count).to_equal(1)
expect(snapshot.fault).to_equal("")
```

</details>

#### should stay on the CPU without device traffic in cpu reference mode

- should stay on the CPU without device traffic in cpu reference mode
   - Expected: snapshot.receipt.stage equals `layout`
   - Expected: snapshot.receipt.bytes_read equals `0`
   - Expected: snapshot.receipt.bytes_written equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should stay on the CPU without device traffic in cpu reference mode")
val nodes = profile_fixture_nodes()
val snapshot = layout_run_full(
    cpu_input(nodes, [], [], 4, []),
    layout_text_measure_port_unavailable()
)

expect(snapshot.receipt.stage).to_equal("layout")
expect(snapshot.receipt.bytes_read).to_equal(0)
expect(snapshot.receipt.bytes_written).to_equal(0)
assert_false(snapshot.execution_proof.submitted)
assert_false(snapshot.execution_proof.device_readback)
```

</details>

#### should map every laid-out island into the layout mapping graph

- should map every laid-out island into the layout mapping graph
   - Expected: snapshot.mappings.len() equals `nodes.len()`
   - Expected: snapshot.island_costs.len() equals `nodes.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should map every laid-out island into the layout mapping graph")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8185e924dbf56af13d6398eab485dfd898c7f99c3e96b53f41502fb3f6b1b746`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8185e924dbf56af13d6398eab485dfd898c7f99c3e96b53f41502fb3f6b1b746`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8185e924dbf56af13d6398eab485dfd898c7f99c3e96b53f41502fb3f6b1b746`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **82/100**; blockers: **0**.

SSpec documentization score: 82/100
source: test/01_unit/lib/structural/layout/layout_cpu_reference_oracle_spec.spl
mirror: doc/06_spec/01_unit/lib/structural/layout/layout_cpu_reference_oracle_spec.md (current)
findings: 12 blockers: 0
  narrative=100 structure=70 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/structural/layout/layout_cpu_reference_oracle_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/structural/layout/layout_cpu_reference_oracle_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/structural/layout/layout_cpu_reference_oracle_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 15 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/structural/layout/layout_cpu_reference_oracle_spec.spl:118:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should produce an empty converged snapshot for an empty input' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/structural/layout/layout_cpu_reference_oracle_spec.spl:118:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should produce an empty converged snapshot for an empty input' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/structural/layout/layout_cpu_reference_oracle_spec.spl:140:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should match the CPU oracle geometry for every profile fixture' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/structural/layout/layout_cpu_reference_oracle_spec.spl:140:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should match the CPU oracle geometry for every profile fixture' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/structural/layout/layout_cpu_reference_oracle_spec.spl:158:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should emit one principal fragment and overflow per laid-out box' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/structural/layout/layout_cpu_reference_oracle_spec.spl:158:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should emit one principal fragment and overflow per laid-out box' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/structural/layout/layout_cpu_reference_oracle_spec.spl:174:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should be deterministic across repeated identical runs' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/structural/layout/layout_cpu_reference_oracle_spec.spl:186:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should yield identical geometry from incremental and full layout' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/structural/layout/layout_cpu_reference_oracle_spec.spl:203:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should visit only the invalidated island during incremental layout' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
