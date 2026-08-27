# Window Scene Draw Ir Layer Order Specification

> Tests covering window scene Draw IR z-layer ordering.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Window Scene Draw Ir Layer Order Specification

## Scenarios

### window scene Draw IR z-layer ordering

#### orders visible window batches by z-index with stable equal-layer order

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- orders visible window batches by z-index with stable equal-layer order
   - Expected: composition.batches.len() equals `7`
   - Expected: composition.batches[2].embedding.surface_id equals `bottom`
   - Expected: composition.batches[3].embedding.surface_id equals `middle-a`
   - Expected: composition.batches[4].embedding.surface_id equals `middle-b`
   - Expected: composition.batches[5].embedding.surface_id equals `top`
   - Expected: composition.batches[6].embedding.component_id equals `wm-taskbar-objects`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("orders visible window batches by z-index with stable equal-layer order")
val composition = shared_wm_scene_draw_ir_composition(_layered_scene(), _taskbar(), DRAW_IR_BACKEND_GPU, 1000, "09:41", 2)

expect(composition.batches.len()).to_equal(7)
expect(composition.batches[2].embedding.surface_id).to_equal("bottom")
expect(composition.batches[3].embedding.surface_id).to_equal("middle-a")
expect(composition.batches[4].embedding.surface_id).to_equal("middle-b")
expect(composition.batches[5].embedding.surface_id).to_equal("top")
expect(composition.batches[6].embedding.component_id).to_equal("wm-taskbar-objects")
```

</details>

#### orders sparse z-index windows without losing stable equal-layer order

- orders sparse z-index windows without losing stable equal-layer order
   - Expected: composition.batches.len() equals `7`
   - Expected: composition.batches[2].embedding.surface_id equals `bottom`
   - Expected: composition.batches[3].embedding.surface_id equals `middle-a`
   - Expected: composition.batches[4].embedding.surface_id equals `middle-b`
   - Expected: composition.batches[5].embedding.surface_id equals `top`
   - Expected: composition.batches[6].embedding.component_id equals `wm-taskbar-objects`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("orders sparse z-index windows without losing stable equal-layer order")
val composition = shared_wm_scene_draw_ir_composition(_sparse_layered_scene(), _taskbar(), DRAW_IR_BACKEND_GPU, 1000, "09:41", 2)

expect(composition.batches.len()).to_equal(7)
expect(composition.batches[2].embedding.surface_id).to_equal("bottom")
expect(composition.batches[3].embedding.surface_id).to_equal("middle-a")
expect(composition.batches[4].embedding.surface_id).to_equal("middle-b")
expect(composition.batches[5].embedding.surface_id).to_equal("top")
expect(composition.batches[6].embedding.component_id).to_equal("wm-taskbar-objects")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/window_scene_draw_ir_layer_order_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering window scene Draw IR z-layer ordering.
- window scene Draw IR z-layer ordering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `6dec52165755d68a97056a67908285435b264abe4a283dafc6b65fc7e046bad9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6dec52165755d68a97056a67908285435b264abe4a283dafc6b65fc7e046bad9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6dec52165755d68a97056a67908285435b264abe4a283dafc6b65fc7e046bad9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/common/ui/window_scene_draw_ir_layer_order_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/window_scene_draw_ir_layer_order_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/window_scene_draw_ir_layer_order_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/window_scene_draw_ir_layer_order_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/window_scene_draw_ir_layer_order_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/ui/window_scene_draw_ir_layer_order_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'orders visible window batches by z-index with stable equal-layer order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/window_scene_draw_ir_layer_order_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'orders sparse z-index windows without losing stable equal-layer order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
