# Draw Ir V3 Execution Route Specification

> Tests covering DrawIR v3 execution route selection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Draw Ir V3 Execution Route Specification

## Scenarios

### DrawIR v3 execution route selection

#### should route an empty scene to the CPU as a policy choice, not a fallback

- should route an empty scene to the CPU as a policy choice, not a fallback
- Select a route for a scene with no commands under a balanced profile
   - Expected: decision.command_count equals `0`
   - Expected: decision.route equals `GPU_ROUTE_CPU_SELECTED`
   - Expected: decision.reason_code equals `DRAW_IR_V3_REASON_EMPTY_SCENE`
   - Expected: draw_ir_v3_route_is_gpu_fallback(decision) is false
   - Expected: draw_ir_v3_route_decision_is_consistent(decision) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should route an empty scene to the CPU as a policy choice, not a fallback")
step("Select a route for a scene with no commands under a balanced profile")
val profile = draw_ir_v3_profile_balanced(4)
val decision = draw_ir_v3_route_select(
    profile, draw_ir_v3_empty_scene(1u32, 1u32), _caps_tier1(), true)

expect(decision.command_count).to_equal(0)
expect(decision.route).to_equal(GPU_ROUTE_CPU_SELECTED)
expect(decision.reason_code).to_equal(DRAW_IR_V3_REASON_EMPTY_SCENE)
expect(draw_ir_v3_route_is_gpu_fallback(decision)).to_equal(false)
expect(draw_ir_v3_route_decision_is_consistent(decision)).to_equal(true)
```

</details>

#### should distinguish a cost-policy CPU route from a denied GPU route

- should distinguish a cost-policy CPU route from a denied GPU route
- Route a small scene on a capable device, then the same scene with no device
- Both ran on the CPU, but the route and the reason must differ
   - Expected: draw_ir_v3_route_is_cpu_selected(by_cost) is true
   - Expected: draw_ir_v3_route_is_gpu_fallback(by_cost) is false
   - Expected: by_cost.reason_code equals `DRAW_IR_V3_REASON_COST_BELOW_THRESHOLD`
   - Expected: draw_ir_v3_route_is_gpu_fallback(by_denial) is true
   - Expected: draw_ir_v3_route_is_cpu_selected(by_denial) is false
   - Expected: by_denial.reason_code equals `DRAW_IR_V3_REASON_NO_DEVICE`
   - Expected: by_cost.route == by_denial.route is false
   - Expected: by_cost.fallback_level equals `GPU_FALLBACK_L0_GPU_NATIVE`
   - Expected: by_denial.fallback_level equals `GPU_FALLBACK_L4_DOCUMENT_COMPAT`
- Neither decision may pair a route with the other class's reason
   - Expected: draw_ir_v3_route_decision_is_consistent(by_cost) is true
   - Expected: draw_ir_v3_route_decision_is_consistent(by_denial) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should distinguish a cost-policy CPU route from a denied GPU route")
step("Route a small scene on a capable device, then the same scene with no device")
val profile = draw_ir_v3_profile_balanced(10)
val scene = _scene_with_rects(3)

val by_cost = draw_ir_v3_route_select(profile, scene, _caps_tier1(), true)
val by_denial = draw_ir_v3_route_select(profile, scene, _caps_tier1(), false)

step("Both ran on the CPU, but the route and the reason must differ")
expect(draw_ir_v3_route_is_cpu_selected(by_cost)).to_equal(true)
expect(draw_ir_v3_route_is_gpu_fallback(by_cost)).to_equal(false)
expect(by_cost.reason_code).to_equal(DRAW_IR_V3_REASON_COST_BELOW_THRESHOLD)

expect(draw_ir_v3_route_is_gpu_fallback(by_denial)).to_equal(true)
expect(draw_ir_v3_route_is_cpu_selected(by_denial)).to_equal(false)
expect(by_denial.reason_code).to_equal(DRAW_IR_V3_REASON_NO_DEVICE)

expect(by_cost.route == by_denial.route).to_equal(false)
expect(by_cost.fallback_level).to_equal(GPU_FALLBACK_L0_GPU_NATIVE)
expect(by_denial.fallback_level).to_equal(GPU_FALLBACK_L4_DOCUMENT_COMPAT)

step("Neither decision may pair a route with the other class's reason")
expect(draw_ir_v3_route_decision_is_consistent(by_cost)).to_equal(true)
expect(draw_ir_v3_route_decision_is_consistent(by_denial)).to_equal(true)
```

</details>

#### should name the cpu_selected and gpu_fallback routes differently in a reason receipt

- should name the cpu_selected and gpu_fallback routes differently in a reason receipt
- Render reason receipts for a cost-policy route and a denial route
   - Expected: draw_ir_v3_route_name(by_cost.route) equals `cpu_selected`
   - Expected: draw_ir_v3_reason_name(by_cost.reason_code) equals `cost_below_threshold`
   - Expected: draw_ir_v3_route_name(by_denial.route) equals `gpu_fallback`
   - Expected: draw_ir_v3_reason_name(by_denial.reason_code) equals `no_device`
- The rendered receipts themselves must not be identical
   - Expected: cost_receipt == denial_receipt is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should name the cpu_selected and gpu_fallback routes differently in a reason receipt")
step("Render reason receipts for a cost-policy route and a denial route")
val profile = draw_ir_v3_profile_balanced(10)
val scene = _scene_with_rects(2)
val by_cost = draw_ir_v3_route_select(profile, scene, _caps_tier1(), true)
val by_denial = draw_ir_v3_route_select(profile, scene, _caps_tier1(), false)

expect(draw_ir_v3_route_name(by_cost.route)).to_equal("cpu_selected")
expect(draw_ir_v3_reason_name(by_cost.reason_code)).to_equal("cost_below_threshold")
expect(draw_ir_v3_route_name(by_denial.route)).to_equal("gpu_fallback")
expect(draw_ir_v3_reason_name(by_denial.reason_code)).to_equal("no_device")

step("The rendered receipts themselves must not be identical")
val cost_receipt = draw_ir_v3_route_reason_receipt(by_cost)
val denial_receipt = draw_ir_v3_route_reason_receipt(by_denial)
expect(cost_receipt == denial_receipt).to_equal(false)
```

</details>

#### should route to the GPU when the scene is large enough and the device is capable

- should route to the GPU when the scene is large enough and the device is capable
- Route a scene above the cost threshold on a tier-1 device
   - Expected: decision.route equals `GPU_ROUTE_GPU`
   - Expected: decision.executed_mode equals `DRAW_IR_V3_MODE_HYBRID_VECTOR_GPU`
   - Expected: draw_ir_v3_route_is_cpu_selected(decision) is false
   - Expected: draw_ir_v3_route_is_gpu_fallback(decision) is false
   - Expected: draw_ir_v3_route_decision_is_consistent(decision) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should route to the GPU when the scene is large enough and the device is capable")
step("Route a scene above the cost threshold on a tier-1 device")
val profile = draw_ir_v3_profile_balanced(2)
val decision = draw_ir_v3_route_select(
    profile, _scene_with_rects(5), _caps_tier1(), true)

expect(decision.route).to_equal(GPU_ROUTE_GPU)
expect(decision.executed_mode).to_equal(DRAW_IR_V3_MODE_HYBRID_VECTOR_GPU)
expect(draw_ir_v3_route_is_cpu_selected(decision)).to_equal(false)
expect(draw_ir_v3_route_is_gpu_fallback(decision)).to_equal(false)
expect(draw_ir_v3_route_decision_is_consistent(decision)).to_equal(true)
```

</details>

#### should serve a cpu-only profile with no GPU present

- should serve a cpu-only profile with no GPU present
- Route under the cpu-only profile with device_available false
   - Expected: draw_ir_v3_route_is_cpu_selected(decision) is true
   - Expected: decision.reason_code equals `DRAW_IR_V3_REASON_MODE_IS_CPU_REFERENCE`
   - Expected: draw_ir_v3_route_is_gpu_fallback(decision) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should serve a cpu-only profile with no GPU present")
step("Route under the cpu-only profile with device_available false")
val decision = draw_ir_v3_route_select(
    draw_ir_v3_profile_cpu_only(), _scene_with_rects(4), 0u32, false)

expect(draw_ir_v3_route_is_cpu_selected(decision)).to_equal(true)
expect(decision.reason_code).to_equal(DRAW_IR_V3_REASON_MODE_IS_CPU_REFERENCE)
expect(draw_ir_v3_route_is_gpu_fallback(decision)).to_equal(false)
```

</details>

#### should deny a resident-GPU profile on a device missing the indirect-dispatch tier

- should deny a resident-GPU profile on a device missing the indirect-dispatch tier
- Route the full-offload profile against a tier-0-only device
   - Expected: draw_ir_v3_route_is_gpu_fallback(decision) is true
   - Expected: decision.reason_code equals `DRAW_IR_V3_REASON_MISSING_CAPABILITY`
   - Expected: decision.missing_capabilities equals `DRAW_IR_V3_CAP_INDIRECT_DISPATCH`
   - Expected: decision.strict_pass is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should deny a resident-GPU profile on a device missing the indirect-dispatch tier")
step("Route the full-offload profile against a tier-0-only device")
val decision = draw_ir_v3_route_select(
    draw_ir_v3_profile_full_offload(), _scene_with_rects(6), _caps_tier0(), true)

expect(draw_ir_v3_route_is_gpu_fallback(decision)).to_equal(true)
expect(decision.reason_code).to_equal(DRAW_IR_V3_REASON_MISSING_CAPABILITY)
expect(decision.missing_capabilities).to_equal(DRAW_IR_V3_CAP_INDIRECT_DISPATCH)
expect(decision.strict_pass).to_equal(false)
```

</details>

#### should let a strict full-offload profile pass only on a native GPU route

- should let a strict full-offload profile pass only on a native GPU route
- Route the full-offload profile against a fully capable device
   - Expected: decision.route equals `GPU_ROUTE_GPU`
   - Expected: decision.executed_mode equals `DRAW_IR_V3_MODE_RESIDENT_GPU`
   - Expected: decision.strict_pass is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should let a strict full-offload profile pass only on a native GPU route")
step("Route the full-offload profile against a fully capable device")
val decision = draw_ir_v3_route_select(
    draw_ir_v3_profile_full_offload(), _scene_with_rects(6), _caps_tier1(), true)

expect(decision.route).to_equal(GPU_ROUTE_GPU)
expect(decision.executed_mode).to_equal(DRAW_IR_V3_MODE_RESIDENT_GPU)
expect(decision.strict_pass).to_equal(true)
```

</details>

#### should report a mid-submission device fault at the device-recovery level

- should report a mid-submission device fault at the device-recovery level
- Build a device-fault decision for a balanced profile
   - Expected: draw_ir_v3_route_is_gpu_fallback(decision) is true
   - Expected: decision.fallback_level equals `GPU_FALLBACK_L5_DEVICE_RECOVERY`
   - Expected: draw_ir_v3_route_decision_is_consistent(decision) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should report a mid-submission device fault at the device-recovery level")
step("Build a device-fault decision for a balanced profile")
val decision = draw_ir_v3_route_device_fault(draw_ir_v3_profile_balanced(2), 9)

expect(draw_ir_v3_route_is_gpu_fallback(decision)).to_equal(true)
expect(decision.fallback_level).to_equal(GPU_FALLBACK_L5_DEVICE_RECOVERY)
expect(draw_ir_v3_route_decision_is_consistent(decision)).to_equal(true)
```

</details>

#### should report a capacity denial as a document-level gpu_fallback

- should report a capacity denial as a document-level gpu_fallback
- Reject a plan through the frozen Kernel C verifier, then deny the route
   - Expected: verdict.accepted is false
   - Expected: draw_ir_v3_route_is_gpu_fallback(decision) is true
   - Expected: decision.reason_code equals `DRAW_IR_V3_REASON_CAPACITY_OVERFLOW`
   - Expected: decision.fallback_level equals `GPU_FALLBACK_L4_DOCUMENT_COMPAT`
   - Expected: draw_ir_v3_route_decision_is_consistent(decision) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should report a capacity denial as a document-level gpu_fallback")
step("Reject a plan through the frozen Kernel C verifier, then deny the route")
val verdict = _verdict_rejected()
val decision = draw_ir_v3_route_capacity_denial(
    draw_ir_v3_profile_balanced(2), verdict, 40)

expect(verdict.accepted).to_equal(false)
expect(draw_ir_v3_route_is_gpu_fallback(decision)).to_equal(true)
expect(decision.reason_code).to_equal(DRAW_IR_V3_REASON_CAPACITY_OVERFLOW)
expect(decision.fallback_level).to_equal(GPU_FALLBACK_L4_DOCUMENT_COMPAT)
expect(draw_ir_v3_route_decision_is_consistent(decision)).to_equal(true)
```

</details>

#### should name the breached manifest bound in the route decision and receipt

- should name the breached manifest bound in the route decision and receipt
- Carry GpuWebCapacityVerdict.first_breach_bound into the route receipt
   - Expected: verdict.first_breach_bound equals `max_draw_commands`
   - Expected: decision.capacity_breach_bound equals `max_draw_commands`
   - Expected: draw_ir_v3_route_reason_receipt(decision) equals `expected_receipt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should name the breached manifest bound in the route decision and receipt")
step("Carry GpuWebCapacityVerdict.first_breach_bound into the route receipt")
val verdict = _verdict_rejected()
val decision = draw_ir_v3_route_capacity_denial(
    draw_ir_v3_profile_balanced(2), verdict, 4096)

expect(verdict.first_breach_bound).to_equal("max_draw_commands")
expect(decision.capacity_breach_bound).to_equal("max_draw_commands")
val expected_receipt = "gpu_fallback reason=capacity_overflow level=L4 commands=4096 bound=max_draw_commands"
expect(draw_ir_v3_route_reason_receipt(decision)).to_equal(expected_receipt)
```

</details>

#### should leave a GPU route untouched when the capacity verdict accepts

- should leave a GPU route untouched when the capacity verdict accepts
- Apply an accepted verdict to a GPU route
   - Expected: routed.route equals `GPU_ROUTE_GPU`
   - Expected: applied.route equals `GPU_ROUTE_GPU`
   - Expected: applied.reason_code equals `routed.reason_code`
   - Expected: applied.capacity_breach_bound equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should leave a GPU route untouched when the capacity verdict accepts")
step("Apply an accepted verdict to a GPU route")
val profile = draw_ir_v3_profile_balanced(2)
val scene = _scene_with_rects(8)
val routed = draw_ir_v3_route_select(profile, scene, _caps_tier1(), true)
val applied = draw_ir_v3_route_apply_capacity(profile, routed, _verdict_accepted())

expect(routed.route).to_equal(GPU_ROUTE_GPU)
expect(applied.route).to_equal(GPU_ROUTE_GPU)
expect(applied.reason_code).to_equal(routed.reason_code)
expect(applied.capacity_breach_bound).to_equal("")
```

</details>

#### should turn a GPU route into a capacity denial when the verdict rejects

- should turn a GPU route into a capacity denial when the verdict rejects
- Apply a rejecting verdict to a GPU route
   - Expected: routed.route equals `GPU_ROUTE_GPU`
   - Expected: applied.route equals `GPU_ROUTE_GPU_FALLBACK`
   - Expected: applied.reason_code equals `DRAW_IR_V3_REASON_CAPACITY_OVERFLOW`
   - Expected: applied.capacity_breach_bound equals `max_draw_commands`
   - Expected: applied.command_count equals `routed.command_count`
   - Expected: draw_ir_v3_route_decision_is_consistent(applied) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should turn a GPU route into a capacity denial when the verdict rejects")
step("Apply a rejecting verdict to a GPU route")
val profile = draw_ir_v3_profile_balanced(2)
val scene = _scene_with_rects(8)
val routed = draw_ir_v3_route_select(profile, scene, _caps_tier1(), true)
val applied = draw_ir_v3_route_apply_capacity(profile, routed, _verdict_rejected())

expect(routed.route).to_equal(GPU_ROUTE_GPU)
expect(applied.route).to_equal(GPU_ROUTE_GPU_FALLBACK)
expect(applied.reason_code).to_equal(DRAW_IR_V3_REASON_CAPACITY_OVERFLOW)
expect(applied.capacity_breach_bound).to_equal("max_draw_commands")
expect(applied.command_count).to_equal(routed.command_count)
expect(draw_ir_v3_route_decision_is_consistent(applied)).to_equal(true)
```

</details>

#### should not overwrite a route that already carries a reason

- should not overwrite a route that already carries a reason
- Apply a rejecting verdict to a no-device denial and to a policy CPU route
   - Expected: denied_applied.reason_code equals `DRAW_IR_V3_REASON_NO_DEVICE`
   - Expected: policy_applied.reason_code equals `DRAW_IR_V3_REASON_COST_BELOW_THRESHOLD`
   - Expected: policy_applied.route equals `GPU_ROUTE_CPU_SELECTED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should not overwrite a route that already carries a reason")
step("Apply a rejecting verdict to a no-device denial and to a policy CPU route")
val strict = draw_ir_v3_profile_full_offload()
val scene = _scene_with_rects(8)
val denied = draw_ir_v3_route_select(strict, scene, _caps_tier1(), false)
val denied_applied = draw_ir_v3_route_apply_capacity(
    strict, denied, _verdict_rejected())

val balanced = draw_ir_v3_profile_balanced(100)
val small = _scene_with_rects(3)
val policy = draw_ir_v3_route_select(balanced, small, _caps_tier1(), true)
val policy_applied = draw_ir_v3_route_apply_capacity(
    balanced, policy, _verdict_rejected())

expect(denied_applied.reason_code).to_equal(DRAW_IR_V3_REASON_NO_DEVICE)
expect(policy_applied.reason_code).to_equal(DRAW_IR_V3_REASON_COST_BELOW_THRESHOLD)
expect(policy_applied.route).to_equal(GPU_ROUTE_CPU_SELECTED)
```

</details>

#### should reject a capacity denial that names no breached bound

- should reject a capacity denial that names no breached bound
- A denial built from an ACCEPTED verdict must fail the partition guard
   - Expected: manufactured.capacity_breach_bound equals ``
   - Expected: draw_ir_v3_route_decision_is_consistent(manufactured) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should reject a capacity denial that names no breached bound")
step("A denial built from an ACCEPTED verdict must fail the partition guard")
val manufactured = draw_ir_v3_route_capacity_denial(
    draw_ir_v3_profile_balanced(2), _verdict_accepted(), 8)

expect(manufactured.capacity_breach_bound).to_equal("")
expect(draw_ir_v3_route_decision_is_consistent(manufactured)).to_equal(false)
```

</details>

#### should not mark a submission accepted after a gpu_fallback

- should not mark a submission accepted after a gpu_fallback
- Build CPU-reference receipts for a policy route and a denial route
   - Expected: cost_receipt.accepted is true
   - Expected: denial_receipt.accepted is false
   - Expected: cost_receipt.route equals `GPU_ROUTE_CPU_SELECTED`
   - Expected: denial_receipt.route equals `GPU_ROUTE_GPU_FALLBACK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should not mark a submission accepted after a gpu_fallback")
step("Build CPU-reference receipts for a policy route and a denial route")
val profile = draw_ir_v3_profile_balanced(10)
val scene = _scene_with_rects(3)
val cost_receipt = draw_ir_v3_route_cpu_reference_receipt(
    scene, 3u64, draw_ir_v3_route_select(profile, scene, _caps_tier1(), true), 12u64)
val denial_receipt = draw_ir_v3_route_cpu_reference_receipt(
    scene, 3u64, draw_ir_v3_route_select(profile, scene, _caps_tier1(), false), 12u64)

expect(cost_receipt.accepted).to_equal(true)
expect(denial_receipt.accepted).to_equal(false)
expect(cost_receipt.route).to_equal(GPU_ROUTE_CPU_SELECTED)
expect(denial_receipt.route).to_equal(GPU_ROUTE_GPU_FALLBACK)
```

</details>

#### should produce a mode-independent deterministic hash for the same scene

- should produce a mode-independent deterministic hash for the same scene
- Hash one scene through a cpu-only route and a GPU route
   - Expected: cpu_receipt.deterministic_hash_lo equals `gpu_receipt.deterministic_hash_lo`
   - Expected: cpu_receipt.route == gpu_receipt.route is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should produce a mode-independent deterministic hash for the same scene")
step("Hash one scene through a cpu-only route and a GPU route")
val scene = _scene_with_rects(4)
val cpu_receipt = draw_ir_v3_route_cpu_reference_receipt(
    scene,
    3u64,
    draw_ir_v3_route_select(draw_ir_v3_profile_cpu_only(), scene, 0u32, false),
    1u64)
val gpu_receipt = draw_ir_v3_route_cpu_reference_receipt(
    scene,
    3u64,
    draw_ir_v3_route_select(draw_ir_v3_profile_balanced(2), scene, _caps_tier1(), true),
    1u64)

expect(cpu_receipt.deterministic_hash_lo).to_equal(gpu_receipt.deterministic_hash_lo)
expect(cpu_receipt.route == gpu_receipt.route).to_equal(false)
```

</details>

#### should report exactly the capability bits the device is missing

- should report exactly the capability bits the device is missing
- Diff a tier-1 requirement against a tier-0 device
   - Expected: draw_ir_v3_missing_capabilities(_caps_tier1(), _caps_tier1()) equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should report exactly the capability bits the device is missing")
step("Diff a tier-1 requirement against a tier-0 device")
expect(draw_ir_v3_missing_capabilities(_caps_tier1(), _caps_tier0()))
    .to_equal(DRAW_IR_V3_CAP_INDIRECT_DISPATCH)
expect(draw_ir_v3_missing_capabilities(_caps_tier1(), _caps_tier1())).to_equal(0u32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/draw_ir_v3_execution_route_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering DrawIR v3 execution route selection.
- DrawIR v3 execution route selection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
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

- Canonical SPipe generation for source `075c248e9a2aa7bf98fc78c9bfc556d7d59d08805b560bd73c00a0304af25b3c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `075c248e9a2aa7bf98fc78c9bfc556d7d59d08805b560bd73c00a0304af25b3c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `075c248e9a2aa7bf98fc78c9bfc556d7d59d08805b560bd73c00a0304af25b3c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/ui/draw_ir_v3_execution_route_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/draw_ir_v3_execution_route_spec.md (current)
findings: 12 blockers: 0
  narrative=100 structure=70 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/draw_ir_v3_execution_route_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/draw_ir_v3_execution_route_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/draw_ir_v3_execution_route_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/ui/draw_ir_v3_execution_route_spec.spl:125:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should route an empty scene to the CPU as a policy choice, not a fallback' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/draw_ir_v3_execution_route_spec.spl:125:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should route an empty scene to the CPU as a policy choice, not a fallback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/draw_ir_v3_execution_route_spec.spl:139:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should distinguish a cost-policy CPU route from a denied GPU route' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/draw_ir_v3_execution_route_spec.spl:139:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should distinguish a cost-policy CPU route from a denied GPU route' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/draw_ir_v3_execution_route_spec.spl:166:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should name the cpu_selected and gpu_fallback routes differently in a reason receipt' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/draw_ir_v3_execution_route_spec.spl:166:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should name the cpu_selected and gpu_fallback routes differently in a reason receipt' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/draw_ir_v3_execution_route_spec.spl:185:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should route to the GPU when the scene is large enough and the device is capable' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/draw_ir_v3_execution_route_spec.spl:199:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should serve a cpu-only profile with no GPU present' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/draw_ir_v3_execution_route_spec.spl:210:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should deny a resident-GPU profile on a device missing the indirect-dispatch tier' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
