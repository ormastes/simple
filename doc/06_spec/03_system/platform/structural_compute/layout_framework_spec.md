# Layout framework

> Exercises the consumer-independent layout capsule from deterministic island discovery through bounded scheduling, exact CPU-oracle geometry, incremental selection, provenance, receipts, and cost-qualified backend selection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Layout framework

Exercises the consumer-independent layout capsule from deterministic island discovery through bounded scheduling, exact CPU-oracle geometry, incremental selection, provenance, receipts, and cost-qualified backend selection.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Platform |
| Status | Active |
| Requirements | doc/02_requirements/feature/layout_framework.md |
| Plan | doc/03_plan/sys_test/layout_framework.md |
| Design | doc/05_design/layout_framework.md |
| Source | `test/03_system/platform/structural_compute/layout_framework_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Exercises the consumer-independent layout capsule from deterministic island
discovery through bounded scheduling, exact CPU-oracle geometry, incremental
selection, provenance, receipts, and cost-qualified backend selection.

The fixture geometry is the CPU oracle. A GPU candidate is accepted only when
its execution proof records submission, synchronization, device readback, and
oracle verification. Inline text remains CPU-owned unless exact metrics exist.

**Requirements:** doc/02_requirements/feature/layout_framework.md
**Plan:** doc/03_plan/sys_test/layout_framework.md
**Design:** doc/05_design/layout_framework.md

## Scenarios

### layout framework covering REQ-001 through REQ-010

#### should preserve oracle geometry through full and incremental execution

- should preserve oracle geometry through full and incremental execution
- Discover layout islands
   - Expected: discovery.fault equals ``
   - Expected: discovery.islands.len() equals `3`
   - Expected: discovery.islands[0].node_ids equals `[1, 2]`
   - Expected: discovery.islands[1].node_ids equals `[3]`
   - Expected: discovery.islands[2].node_ids equals `[4]`
- Schedule dirty layout waves
   - Expected: scheduled.converged is true
   - Expected: scheduled.waves[0].island_ids equals `[1, 3, 4]`
- Measure and arrange profiles
   - Expected: incremental.boxes equals `full.boxes`
   - Expected: full.backend equals `serial_cpu`
   - Expected: full.receipt.fallback_reason equals `gpu-execution-unavailable`
- Verify geometry and receipts
   - Expected: full.receipt.input_hash equals `incremental.receipt.input_hash`
   - Expected: full.receipt.output_hash equals `incremental.receipt.output_hash`
   - Expected: full.receipt.deterministic_hash equals `full_again.receipt.deterministic_hash`
- Reject a GPU claim without device readback
   - Expected: rejected_gpu.backend equals `serial_cpu`
   - Expected: rejected_gpu.receipt.candidate_backend equals `hybrid_vector_gpu`
   - Expected: rejected_gpu.receipt.fallback_reason equals `gpu-readback-missing`
   - Expected: rejected_gpu.execution_proof.device_readback is false
   - Expected: rejected_gpu.island_costs.len() equals `rejected_gpu.islands.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 49 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
# @req REQ-001 REQ-002 REQ-003 REQ-004 REQ-005
step("should preserve oracle geometry through full and incremental execution")
val input = layout_fixture_snapshot(layout_profile(200), [3], 4)
val text_port = layout_text_measure_port_unavailable()

step("Discover layout islands")
val discovery = layout_discover_islands(input)
expect(discovery.fault).to_equal("")
expect(discovery.islands.len()).to_equal(3)
expect(discovery.islands[0].node_ids).to_equal([1, 2])
expect(discovery.islands[1].node_ids).to_equal([3])
expect(discovery.islands[2].node_ids).to_equal([4])

step("Schedule dirty layout waves")
val scheduled = layout_schedule_waves(discovery.islands, input.dependencies, input.fixed_point_cap)
expect(scheduled.converged).to_equal(true)
expect(scheduled.waves[0].island_ids).to_equal([1, 3, 4])

step("Measure and arrange profiles")
val full = layout_run_full(input, text_port)
val full_again = layout_run_full(input, text_port)
val incremental = layout_run_incremental(input, text_port)
expect_layout_geometry(full)
expect_layout_geometry(incremental)
expect(incremental.boxes).to_equal(full.boxes)
expect(full.backend).to_equal("serial_cpu")
expect(full.receipt.fallback_reason).to_equal("gpu-execution-unavailable")

step("Verify geometry and receipts")
expect_bounded_fixed_point(full)
expect_bounded_fixed_point(incremental)
expect_dirty_island_receipts(incremental)
expect(full.receipt.input_hash).to_equal(incremental.receipt.input_hash)
expect(full.receipt.output_hash).to_equal(incremental.receipt.output_hash)
expect(full.receipt.deterministic_hash).to_equal(full_again.receipt.deterministic_hash)

step("Reject a GPU claim without device readback")
val rejected_gpu = layout_run_full_with_ports(
    input,
    text_port,
    layout_execution_port_oracle(input.oracle_boxes),
    ClaimOnlyGpuLayoutPort()
)
expect(rejected_gpu.backend).to_equal("serial_cpu")
expect(rejected_gpu.receipt.candidate_backend).to_equal("hybrid_vector_gpu")
expect(rejected_gpu.receipt.fallback_reason).to_equal("gpu-readback-missing")
expect(rejected_gpu.execution_proof.device_readback).to_equal(false)
expect(rejected_gpu.island_costs.len()).to_equal(rejected_gpu.islands.len())
```

</details>

<details>
<summary>Advanced: covers every initial profile with fragments line boxes and overflow</summary>

#### covers every initial profile with fragments line boxes and overflow

- covers every initial profile with fragments line boxes and overflow
   - Expected: result.fault equals ``
   - Expected: result.boxes.len() equals `8`
   - Expected: result.fragments.len() equals `8`
   - Expected: result.line_boxes.len() equals `1`
   - Expected: result.line_boxes[0].text_end equals `4`
   - Expected: result.overflows.len() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
# @req REQ-006 REQ-007
step("covers every initial profile with fragments line boxes and overflow")
val input = layout_input_with_text(
    [
        fixture_node(1, 0, "block", true, false, 0, 8, false),
        fixture_node(2, 0, "inline", true, false, 0, 8, true),
        fixture_node(3, 0, "flex", true, false, 0, 8, false),
        fixture_node(4, 0, "grid", true, false, 0, 8, false),
        fixture_node(5, 0, "table", true, false, 0, 8, false),
        fixture_node(6, 0, "absolute-sticky", true, false, 0, 8, false),
        fixture_node(7, 0, "scroll", true, false, 0, 8, false),
        fixture_node(8, 0, "replaced", true, false, 0, 8, false)
    ],
    [], [], [layout_text_measure_request(2, "text", "sans", 16, "en")],
    layout_execution_profile("serial_cpu", 100, 0, 0, 0, 0, 0, 0, 0), 4,
    80, 160, [], [
        layout_box(1, 0, 0, 80, 20), layout_box(2, 0, 20, 80, 20),
        layout_box(3, 0, 40, 80, 20), layout_box(4, 0, 60, 80, 20),
        layout_box(5, 0, 80, 80, 20), layout_box(6, 0, 100, 80, 20),
        layout_box(7, 0, 120, 80, 20), layout_box(8, 0, 140, 80, 20)
    ]
)
val text_port = layout_text_measure_port_resolved([
    LayoutTextMeasureResult(
        node_id: 2,
        available: true,
        font_identity: "sans-v1",
        width: 32,
        line_height: 20,
        advances: [8, 8, 8, 8],
        reason: ""
    )
])
val result = layout_run_full(input, text_port)
expect(result.fault).to_equal("")
expect(result.boxes.len()).to_equal(8)
expect(result.fragments.len()).to_equal(8)
expect(result.line_boxes.len()).to_equal(1)
expect(result.line_boxes[0].text_end).to_equal(4)
expect(result.overflows.len()).to_equal(8)
```

</details>


</details>

<details>
<summary>Advanced: should fall back for small text unsupported and non-convergent work</summary>

#### should fall back for small text unsupported and non-convergent work

- should fall back for small text unsupported and non-convergent work
   - Expected: layout_run_full(small, layout_text_measure_port_unavailable()).backend equals `serial_cpu`
   - Expected: layout_run_full(small, layout_text_measure_port_unavailable()).receipt.fallback_reason equals `gpu-cost-not-lower`
   - Expected: inline_result.backend equals `serial_cpu`
   - Expected: inline_result.receipt.fallback_reason equals `text-measure-unavailable`
   - Expected: cyclic_result.backend equals `serial_cpu`
   - Expected: cyclic_result.fault equals `non-convergent`
   - Expected: cyclic_result.receipt.fallback_reason equals `non-convergent`
   - Expected: cyclic_result.receipt.iterations equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
# @req REQ-008 REQ-009 REQ-010
step("should fall back for small text unsupported and non-convergent work")
val small = layout_fixture_snapshot(layout_profile(80), [3], 4)
expect(layout_run_full(small, layout_text_measure_port_unavailable()).backend).to_equal("serial_cpu")
expect(layout_run_full(small, layout_text_measure_port_unavailable()).receipt.fallback_reason).to_equal("gpu-cost-not-lower")

val inline_input = layout_input(
    [fixture_node(1, 0, "inline", true, false, 1, 100, true)],
    [], [1], layout_profile(500), 2, 80, 20, [], [layout_box(1, 0, 0, 80, 20)]
)
val inline_result = layout_run_full(inline_input, layout_text_measure_port_unavailable())
expect(inline_result.backend).to_equal("serial_cpu")
expect(inline_result.receipt.fallback_reason).to_equal("text-measure-unavailable")

val cyclic_input = layout_input(
    [
        fixture_node(1, 0, "block", true, false, 1, 50, false),
        fixture_node(2, 0, "block", true, false, 1, 50, false)
    ],
    [
        layout_dependency(1, 2, "percentage", 1),
        layout_dependency(2, 1, "intrinsic-size", 1)
    ],
    [1, 2], layout_profile(500), 2, 40, 20, [], [
        layout_box(1, 0, 0, 20, 20), layout_box(2, 20, 0, 20, 20)
    ]
)
val cyclic_result = layout_run_full_with_ports(
    cyclic_input,
    layout_text_measure_port_unavailable(),
    OscillatingCpuLayoutPort(boxes: cyclic_input.oracle_boxes),
    layout_execution_port_unavailable("hybrid_vector_gpu", "gpu-execution-unavailable")
)
expect(cyclic_result.backend).to_equal("serial_cpu")
expect(cyclic_result.fault).to_equal("non-convergent")
expect(cyclic_result.receipt.fallback_reason).to_equal("non-convergent")
expect(cyclic_result.receipt.iterations).to_equal(2)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/layout_framework.md`
- **Plan:** `doc/03_plan/sys_test/layout_framework.md`
- **Design:** `doc/05_design/layout_framework.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-001`
- `REQ-002`
- `REQ-003`
- `REQ-004`
- `REQ-005`
- `REQ-006`
- `REQ-007`
- `REQ-008`
- `REQ-009`
- `REQ-010`
- `REQ-010":`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4a7f97b8941a7572c8ffb9896ec406c602e1ff2ae5dd74959293f4e86a5cadc4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4a7f97b8941a7572c8ffb9896ec406c602e1ff2ae5dd74959293f4e86a5cadc4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4a7f97b8941a7572c8ffb9896ec406c602e1ff2ae5dd74959293f4e86a5cadc4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **85/100**; blockers: **0**.

SSpec documentization score: 85/100
source: test/03_system/platform/structural_compute/layout_framework_spec.spl
mirror: doc/06_spec/03_system/platform/structural_compute/layout_framework_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=90 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/platform/structural_compute/layout_framework_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/platform/structural_compute/layout_framework_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/platform/structural_compute/layout_framework_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/platform/structural_compute/layout_framework_spec.spl:173:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve oracle geometry through full and incremental execution' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/platform/structural_compute/layout_framework_spec.spl:173:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve oracle geometry through full and incremental execution' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/platform/structural_compute/layout_framework_spec.spl:225:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'covers every initial profile with fragments line boxes and overflow' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/platform/structural_compute/layout_framework_spec.spl:269:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should fall back for small text unsupported and non-convergent work' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/platform/structural_compute/layout_framework_spec.spl:269:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should fall back for small text unsupported and non-convergent work' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
