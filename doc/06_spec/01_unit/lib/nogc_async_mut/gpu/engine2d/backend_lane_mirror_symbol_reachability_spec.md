# Backend Lane Mirror Symbol Reachability Specification

> Tests covering nogc Engine2D backend_lane exports are all actually reachable.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Lane Mirror Symbol Reachability Specification

## Scenarios

### nogc Engine2D backend_lane exports are all actually reachable

#### resolves every lane-constructor export

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- resolves every lane-constructor export


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves every lane-constructor export")
assert_equal(engine2d_drawing_backend_lane("vulkan").lane, ENGINE2D_BACKEND_LANE_DRAWING)
assert_equal(engine2d_processing_backend_lane("cuda").lane, ENGINE2D_BACKEND_LANE_PROCESSING)
assert_equal(engine2d_combined_backend_lane("metal").lane, ENGINE2D_BACKEND_LANE_COMBINED)
```

</details>

#### resolves every summary and plan export

- resolves every summary and plan export


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves every summary and plan export")
val lane = engine2d_drawing_backend_lane("vulkan")
assert_true(engine2d_backend_lane_summary(lane).len() > 0)
assert_true(engine2d_backend_lane_preference_summary().len() > 0)
val plan = engine2d_backend_lane_plan("vulkan", "cuda", true, false)
assert_equal(plan.drawing_backend.backend_name, "vulkan")
assert_equal(plan.processing_backend.backend_name, "cuda")
```

</details>

#### resolves every preference-order export

- resolves every preference-order export


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves every preference-order export")
assert_true(engine2d_backend_lane_full_preference_order().len() > 0)
assert_true(engine2d_backend_lane_drawing_preference_order().len() > 0)
assert_true(engine2d_font_offload_backend_order().len() > 0)
```

</details>

#### resolves both candidate pickers, not just the general one

- resolves both candidate pickers, not just the general one


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves both candidate pickers, not just the general one")
# The general picker was always fine; the font-offload picker was the
# one carrying a gc-only symbol. Both must answer.
assert_equal(engine2d_backend_lane_preferred_candidate(["cpu", "cuda"], false), "cuda")
assert_equal(engine2d_backend_lane_preferred_font_offload_candidate(["cpu", "cuda"]), "cuda")
```

</details>

#### resolves the operation-lane and host-gpu exports

- resolves the operation-lane and host-gpu exports


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves the operation-lane and host-gpu exports")
assert_true(engine2d_operation_lane("glyph_raster").len() > 0)
val schedule = engine2d_host_gpu_lane_schedule(
    ENGINE2D_HOST_GPU_LANE_HOST, ENGINE2D_HOST_GPU_LANE_HOST,
    "glyph_raster", 64, 4096, false, false, true, 5
)
assert_equal(schedule.ok, true)
assert_true(engine2d_host_gpu_lane_summary(schedule).len() > 0)
```

</details>

#### agrees with the gc mirror on the font-offload backends unique to it

- agrees with the gc mirror on the font-offload backends unique to it


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("agrees with the gc mirror on the font-offload backends unique to it")
# qualcomm and intel exist ONLY in the font-offload order, not in the
# general preference order — exactly the pair the partial port dropped.
for backend in ["qualcomm", "intel"]:
    assert_equal(engine2d_backend_lane_preferred_font_offload_candidate([backend]), backend)
    assert_equal(engine2d_backend_lane_preferred_candidate([backend], false), "")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/gpu/engine2d/backend_lane_mirror_symbol_reachability_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc Engine2D backend_lane exports are all actually reachable.
- nogc Engine2D backend_lane exports are all actually reachable

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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ef8b39c5d9463d483909a041cc2199df8b57b7ecf60713d47e76d22f24ef7e2f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ef8b39c5d9463d483909a041cc2199df8b57b7ecf60713d47e76d22f24ef7e2f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ef8b39c5d9463d483909a041cc2199df8b57b7ecf60713d47e76d22f24ef7e2f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_async_mut/gpu/engine2d/backend_lane_mirror_symbol_reachability_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/gpu/engine2d/backend_lane_mirror_symbol_reachability_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/gpu/engine2d/backend_lane_mirror_symbol_reachability_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/gpu/engine2d/backend_lane_mirror_symbol_reachability_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/gpu/engine2d/backend_lane_mirror_symbol_reachability_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves every lane-constructor export' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/gpu/engine2d/backend_lane_mirror_symbol_reachability_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves every summary and plan export' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/gpu/engine2d/backend_lane_mirror_symbol_reachability_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves every preference-order export' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
