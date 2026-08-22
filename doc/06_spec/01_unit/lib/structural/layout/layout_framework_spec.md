# layout_framework_spec

> Verifies the layout framework behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# layout_framework_spec

Verifies the layout framework behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/structural/layout/layout_framework_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the layout framework behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### layout framework unit contract

#### should preserve versioned flat input values

- Verify: should preserve versioned flat input values
   - Expected: input.contract_version equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: input.oracle_boxes[0] equals `box`
   - Expected: input.nodes[0].dirty_bits equals `5)  # oracle: pinned constant asserted by this scenario`
   - Expected: input.nodes[0].dirty.bits equals `5)  # oracle: pinned constant asserted by this scenario`
   - Expected: input.dependencies[0].kind equals `intrinsic-size`
   - Expected: input.dependencies[0].invalidates.bits equals `4)  # oracle: pinned constant asserted by this scenario`
   - Expected: input.invalidated_ids equals `[7]`
   - Expected: input.fixed_point_cap equals `4)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-004 REQ-005 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: should preserve versioned flat input values")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val box = layout_box(7, 10, 20, 300, 40)
val node = layout_node(7, 0, "block", true, false, 5, 9, false, layout_node_semantics_default("block"))
val dependency = layout_dependency(7, 8, "intrinsic-size", 4)
val input = layout_input([node], [dependency], [7], unit_execution("serial_cpu", 80, 30, 10), 4, 0, 0, [], [box])

expect(input.contract_version).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(input.oracle_boxes[0]).to_equal(box)
expect(input.nodes[0].dirty_bits).to_equal(5)  # oracle: pinned constant asserted by this scenario
expect(input.nodes[0].dirty.bits).to_equal(5)  # oracle: pinned constant asserted by this scenario
expect(input.dependencies[0].kind).to_equal("intrinsic-size")
expect(input.dependencies[0].invalidates.bits).to_equal(4)  # oracle: pinned constant asserted by this scenario
expect(input.invalidated_ids).to_equal([7])
expect(input.fixed_point_cap).to_equal(4)  # oracle: pinned constant asserted by this scenario
```

</details>

#### should expose the complete serial profile catalog

- Verify: should expose the complete serial profile catalog
   - Expected: catalog.len() equals `8)  # oracle: pinned constant asserted by this scenario`
   - Expected: catalog[0].profile_id() equals `block`
   - Expected: catalog[1].profile_id() equals `inline`
   - Expected: catalog[2].profile_id() equals `flex`
   - Expected: catalog[3].profile_id() equals `grid`
   - Expected: catalog[4].profile_id() equals `table`
   - Expected: catalog[5].profile_id() equals `absolute-sticky`
   - Expected: catalog[6].profile_id() equals `scroll`
   - Expected: catalog[7].profile_id() equals `replaced`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-004 REQ-005 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: should expose the complete serial profile catalog")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val catalog = layout_profile_catalog()
expect(catalog.len()).to_equal(8)  # oracle: pinned constant asserted by this scenario
expect(catalog[0].profile_id()).to_equal("block")
expect(catalog[1].profile_id()).to_equal("inline")
expect(catalog[2].profile_id()).to_equal("flex")
expect(catalog[3].profile_id()).to_equal("grid")
expect(catalog[4].profile_id()).to_equal("table")
expect(catalog[5].profile_id()).to_equal("absolute-sticky")
expect(catalog[6].profile_id()).to_equal("scroll")
expect(catalog[7].profile_id()).to_equal("replaced")
```

</details>

#### should discover stable boundary and containment islands

- Verify: should discover stable boundary and containment islands
   - Expected: first.fault equals ``
   - Expected: first.islands equals `second.islands`
   - Expected: first.islands.len() equals `3)  # oracle: pinned constant asserted by this scenario`
   - Expected: first.islands[0].node_ids equals `[1, 2]`
   - Expected: first.islands[0].estimated_work equals `15)  # oracle: pinned constant asserted by this scenario`
   - Expected: first.islands[1].node_ids equals `[3]`
   - Expected: first.islands[2].node_ids equals `[4]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-004 REQ-005 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: should discover stable boundary and containment islands")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val nodes = [
    unit_node(1, 0, "block", true, false, 10),
    unit_node(2, 1, "block", false, false, 5),
    unit_node(3, 1, "flex", true, false, 20),
    unit_node(4, 3, "grid", false, true, 30)
]
val input = unit_input(nodes, [], 4)
val first = layout_discover_islands(input)
val second = layout_discover_islands(input)

expect(first.fault).to_equal("")
expect(first.islands).to_equal(second.islands)
expect(first.islands.len()).to_equal(3)  # oracle: pinned constant asserted by this scenario
expect(first.islands[0].node_ids).to_equal([1, 2])
expect(first.islands[0].estimated_work).to_equal(15)  # oracle: pinned constant asserted by this scenario
expect(first.islands[1].node_ids).to_equal([3])
expect(first.islands[2].node_ids).to_equal([4])
```

</details>

#### should condense cycles and emit deterministic topological waves

- Verify: should condense cycles and emit deterministic topological waves
   - Expected: scheduled.converged is true
   - Expected: scheduled.reason equals ``
   - Expected: scheduled.iterations equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: scheduled.cyclic_island_ids equals `[2, 3]`
   - Expected: scheduled.waves.len() equals `3)  # oracle: pinned constant asserted by this scenario`
   - Expected: scheduled.waves[0].island_ids equals `[1]`
   - Expected: scheduled.waves[1].island_ids equals `[2, 3]`
   - Expected: scheduled.waves[2].island_ids equals `[4]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-004 REQ-005 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: should condense cycles and emit deterministic topological waves")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val nodes = [
    unit_node(1, 0, "block", true, false, 10),
    unit_node(2, 0, "block", true, false, 10),
    unit_node(3, 0, "block", true, false, 10),
    unit_node(4, 0, "block", true, false, 10)
]
val dependencies = [
    layout_dependency(1, 2, "containing-block", 1),
    layout_dependency(2, 3, "percentage", 1),
    layout_dependency(3, 2, "baseline", 1),
    layout_dependency(3, 4, "track-column", 1)
]
val islands = layout_discover_islands(unit_input(nodes, dependencies, 3)).islands
val scheduled = layout_schedule_waves(islands, dependencies, 3)

expect(scheduled.converged).to_equal(true)
expect(scheduled.reason).to_equal("")
expect(scheduled.iterations).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(scheduled.cyclic_island_ids).to_equal([2, 3])
expect(scheduled.waves.len()).to_equal(3)  # oracle: pinned constant asserted by this scenario
expect(scheduled.waves[0].island_ids).to_equal([1])
expect(scheduled.waves[1].island_ids).to_equal([2, 3])
expect(scheduled.waves[2].island_ids).to_equal([4])
```

</details>

#### should leave cyclic convergence to execution

- Verify: should leave cyclic convergence to execution
   - Expected: scheduled.converged is true
   - Expected: scheduled.iterations equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: scheduled.cyclic_island_ids equals `[1, 2]`
   - Expected: scheduled.reason equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-004 REQ-005 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: should leave cyclic convergence to execution")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val nodes = [
    unit_node(1, 0, "block", true, false, 10),
    unit_node(2, 0, "block", true, false, 10)
]
val dependencies = [
    layout_dependency(1, 2, "percentage", 1),
    layout_dependency(2, 1, "intrinsic-size", 1)
]
val islands = layout_discover_islands(unit_input(nodes, dependencies, 2)).islands
val scheduled = layout_schedule_waves(islands, dependencies, 2)

expect(scheduled.converged).to_equal(true)
expect(scheduled.iterations).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(scheduled.cyclic_island_ids).to_equal([1, 2])
expect(scheduled.reason).to_equal("")
```

</details>

#### should reject malformed scheduler inputs explicitly

- Verify: should reject malformed scheduler inputs explicitly
   - Expected: layout_schedule_waves(islands, missing, 1).reason equals `missing-dependency-endpoint`
   - Expected: layout_schedule_waves(islands, [], 0).reason equals `invalid-fixed-point-cap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-004 REQ-005 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: should reject malformed scheduler inputs explicitly")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val nodes = [unit_node(1, 0, "block", true, false, 10)]
val missing = [layout_dependency(1, 99, "percentage", 1)]
val islands = layout_discover_islands(unit_input(nodes, missing, 1)).islands

expect(layout_schedule_waves(islands, missing, 1).reason).to_equal("missing-dependency-endpoint")
expect(layout_schedule_waves(islands, [], 0).reason).to_equal("invalid-fixed-point-cap")
```

</details>

#### should propagate incremental dependencies from producer to consumer

- Verify: should propagate incremental dependencies from producer to consumer
   - Expected: result.receipt.mode equals `incremental`
   - Expected: result.receipt.visited_island_ids equals `[1, 2]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-004 REQ-005 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: should propagate incremental dependencies from producer to consumer")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val nodes = [
    unit_node(1, 0, "block", true, false, 10),
    unit_node(2, 1, "block", false, false, 10)
]
val dependencies = [layout_dependency(1, 2, "containing-context", 1)]
val input = layout_input(
    nodes, dependencies, [1], unit_execution("serial_cpu", 80, 30, 10), 4,
    0, 0, [], [
        layout_box(1, 0, 0, 10, 10),
        layout_box(2, 0, 10, 10, 10)
    ]
)
val result = layout_run_incremental(input, layout_text_measure_port_unavailable())

expect(result.receipt.mode).to_equal("incremental")
expect(result.receipt.visited_island_ids).to_equal([1, 2])
```

</details>

#### should include scheduling transfer and synchronization in backend cost

- Verify: should include scheduling transfer and synchronization in backend cost
   - Expected: gpu.gpu_us equals `90)  # oracle: pinned constant asserted by this scenario`
   - Expected: gpu.cpu_us equals `200)  # oracle: pinned constant asserted by this scenario`
   - Expected: gpu.backend equals `hybrid_vector_gpu`
   - Expected: cpu.gpu_us equals `90)  # oracle: pinned constant asserted by this scenario`
   - Expected: cpu.backend equals `serial_cpu`
   - Expected: cpu.reason equals `gpu-cost-not-lower`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-004 REQ-005 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: should include scheduling transfer and synchronization in backend cost")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val nodes = [
    unit_node(1, 0, "grid", true, false, 100),
    unit_node(2, 0, "grid", true, false, 100)
]
val islands = layout_discover_islands(unit_input(nodes, [], 2)).islands
val gpu = layout_choose_backend(islands, layout_execution_profile("hybrid_vector_gpu", 200, 40, 20, 1024, 1024, 2, 10, 5))
val cpu = layout_choose_backend(islands, layout_execution_profile("hybrid_vector_gpu", 80, 40, 20, 1024, 1024, 2, 10, 5))

expect(gpu.gpu_us).to_equal(90)  # oracle: pinned constant asserted by this scenario
expect(gpu.cpu_us).to_equal(200)  # oracle: pinned constant asserted by this scenario
expect(gpu.backend).to_equal("hybrid_vector_gpu")
expect(cpu.gpu_us).to_equal(90)  # oracle: pinned constant asserted by this scenario
expect(cpu.backend).to_equal("serial_cpu")
expect(cpu.reason).to_equal("gpu-cost-not-lower")
```

</details>

#### should keep text and unsupported profiles on the CPU

- Verify: should keep text and unsupported profiles on the CPU
   - Expected: layout_choose_backend(inline_islands, fast_gpu).reason equals `text-measure-required`
   - Expected: layout_choose_backend(table_islands, fast_gpu).reason equals `unsupported-gpu-profile`
   - Expected: layout_choose_backend(inline_islands, fast_gpu).backend equals `serial_cpu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-004 REQ-005 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: should keep text and unsupported profiles on the CPU")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val inline_nodes = [unit_node(1, 0, "inline", true, false, 100)]
val table_nodes = [unit_node(1, 0, "table", true, false, 100)]
val inline_islands = layout_discover_islands(unit_input(inline_nodes, [], 2)).islands
val table_islands = layout_discover_islands(unit_input(table_nodes, [], 2)).islands
val fast_gpu = layout_execution_profile("hybrid_vector_gpu", 500, 10, 5, 0, 0, 0, 0, 0)

expect(layout_choose_backend(inline_islands, fast_gpu).reason).to_equal("text-measure-required")
expect(layout_choose_backend(table_islands, fast_gpu).reason).to_equal("unsupported-gpu-profile")
expect(layout_choose_backend(inline_islands, fast_gpu).backend).to_equal("serial_cpu")
```

</details>

#### should reject heterogeneous GPU batches before execution

- Verify: should reject heterogeneous GPU batches before execution
   - Expected: layout_choose_backend(islands, fast_gpu).backend equals `serial_cpu`
   - Expected: layout_choose_backend(islands, fast_gpu).reason equals `heterogeneous-gpu-batch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-004 REQ-005 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: should reject heterogeneous GPU batches before execution")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val nodes = [
    unit_node(1, 0, "block", true, false, 100),
    unit_node(2, 0, "grid", true, false, 100)
]
val islands = layout_discover_islands(unit_input(nodes, [], 2)).islands
val fast_gpu = layout_execution_profile("hybrid_vector_gpu", 500, 10, 5, 0, 0, 0, 0, 0)
expect(layout_choose_backend(islands, fast_gpu).backend).to_equal("serial_cpu")
expect(layout_choose_backend(islands, fast_gpu).reason).to_equal("heterogeneous-gpu-batch")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `09529f75a974bef49143056af49e7f8d2941b06f21277c26e9972301cc9392e8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `09529f75a974bef49143056af49e7f8d2941b06f21277c26e9972301cc9392e8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `09529f75a974bef49143056af49e7f8d2941b06f21277c26e9972301cc9392e8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/structural/layout/layout_framework_spec.spl
mirror: doc/06_spec/01_unit/lib/structural/layout/layout_framework_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/structural/layout/layout_framework_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/lib/structural/layout/layout_framework_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/structural/layout/layout_framework_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/structural/layout/layout_framework_spec.spl:63:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve versioned flat input values' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/structural/layout/layout_framework_spec.spl:81:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose the complete serial profile catalog' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/structural/layout/layout_framework_spec.spl:96:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should discover stable boundary and containment islands' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/structural/layout/layout_framework_spec.spl:118:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should condense cycles and emit deterministic topological waves' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/structural/layout/layout_framework_spec.spl:146:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should leave cyclic convergence to execution' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/structural/layout/layout_framework_spec.spl:166:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject malformed scheduler inputs explicitly' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
