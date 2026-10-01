# Backend Metal Device Identity Specification

> Tests covering Metal backend owner device identity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Metal Device Identity Specification

## Scenarios

### Metal backend owner device identity

#### keeps one positive owner identity across active glass and device readback when native Metal is available

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps one positive owner identity across active glass and device readback when native Metal is available
   - Expected: native_metal_status equals `unavailable`
   - Expected: engine.backend_name() equals `metal`
   - Expected: execution.applied is true
   - Expected: readback.source equals `device_readback`
   - Expected: readback.pixels.len() equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps one positive owner identity across active glass and device readback when native Metal is available")
var engine = Engine2D.create_with_backend_fast(4, 4, "metal")
if engine.backend_name() != "metal":
    val native_metal_status = "unavailable"
    expect(native_metal_status).to_equal("unavailable")
else:
    expect(engine.backend_name()).to_equal("metal")
    engine.clear(0xFF204060u32)
    val config = Engine2dGlassMaterialConfig(
        framebuffer_width: 4,
        framebuffer_height: 4,
        x: 0,
        y: 0,
        width: 4,
        height: 4,
        radius: 0,
        blur_radius: 0,
        saturation_milli: 1000,
        surface_alpha_milli: 1000,
        surface_color: 0xFFFFFFFFu32,
        gradient_from: 0u32,
        gradient_to: 0u32,
        gradient_enabled: false,
        gradient_layered_over_surface: false
    )
    val execution = engine.draw_ir_apply_glass_material(config)
    expect(execution.applied).to_equal(true)
    expect(execution.execution_target).to_equal(
        "metal-device-glass-v1")
    expect(execution.backend_handle).to_be_greater_than(0)
    expect(execution.device_identity).to_be_greater_than(0)

    val readback = engine.read_pixels_with_source()
    expect(readback.source).to_equal("device_readback")
    expect(readback.backend_handle).to_equal(
        execution.backend_handle)
    expect(readback.device_identity).to_equal(
        execution.device_identity)
    expect(readback.pixels.len()).to_equal(16)
    engine.shutdown()
```

</details>

#### fails closed before device dispatch for inactive 930 native Metal when available

- fails closed before device dispatch for inactive 930 native Metal when available
   - Expected: native_metal_status equals `unavailable`
   - Expected: result.rendered_command_count equals `0`
   - Expected: result.skipped_command_count equals `2`
   - Expected: result.metal_device_glass_material_count equals `0`
   - Expected: result.metal_device_glass_requested_count equals `2`
   - Expected: result.metal_device_glass_unfulfilled_count equals `2`
   - Expected: result.metal_device_glass_receipts.len() equals `2`
   - Expected: body_receipt.fulfilled is false
   - Expected: title_receipt.fulfilled is false
   - Expected: body_receipt.execution_target equals `unavailable`
   - Expected: title_receipt.execution_target equals `unavailable`
   - Expected: body_receipt.backend_handle equals `0`
   - Expected: title_receipt.backend_handle equals `0`
   - Expected: body_receipt.device_identity equals `0`
   - Expected: title_receipt.device_identity equals `0`
   - Expected: result.fallback_required is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails closed before device dispatch for inactive 930 native Metal when available")
var engine = Engine2D.create_with_backend_fast(4, 4, "metal")
if engine.backend_name() != "metal":
    val native_metal_status = "unavailable"
    expect(native_metal_status).to_equal("unavailable")
else:
    val composition = _inactive_metal_composition()
    val result = engine2d_draw_ir_adv_composition(
        engine, composition, true)
    expect(result.rendered_command_count).to_equal(0)
    expect(result.skipped_command_count).to_equal(2)
    expect(result.metal_device_glass_material_count).to_equal(0)
    expect(result.metal_device_glass_requested_count).to_equal(2)
    expect(result.metal_device_glass_unfulfilled_count).to_equal(2)
    expect(result.metal_device_glass_receipts.len()).to_equal(2)
    val body_receipt = result.metal_device_glass_receipts[0]
    val title_receipt = result.metal_device_glass_receipts[1]
    expect(body_receipt.material_id).to_equal(
        "inactive-body-glass")
    expect(title_receipt.material_id).to_equal(
        "inactive-title-glass")
    expect(body_receipt.fulfilled).to_equal(false)
    expect(title_receipt.fulfilled).to_equal(false)
    expect(body_receipt.execution_target).to_equal("unavailable")
    expect(title_receipt.execution_target).to_equal("unavailable")
    expect(body_receipt.backend_handle).to_equal(0)
    expect(title_receipt.backend_handle).to_equal(0)
    expect(body_receipt.device_identity).to_equal(0)
    expect(title_receipt.device_identity).to_equal(0)
    expect(result.fallback_required).to_equal(true)
    expect(result.fallback_reason).to_contain(
        "metal glass material device receipt missing")
    engine.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_device_identity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Metal backend owner device identity.
- Metal backend owner device identity

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

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2382d3b705ae2b60cdb5dc0452e816955e96af7ef7696bf34a2486080461a3e3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2382d3b705ae2b60cdb5dc0452e816955e96af7ef7696bf34a2486080461a3e3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2382d3b705ae2b60cdb5dc0452e816955e96af7ef7696bf34a2486080461a3e3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **72/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_device_identity_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_device_identity_spec.md (current)
findings: 7 blockers: 2
  narrative=100 structure=100 oracle=20
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=72; blocker cap makes effective=49
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_device_identity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_device_identity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_device_identity_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario compares only locally constructed arithmetic or literals
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_device_identity_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_device_identity_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_device_identity_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps one positive owner identity across active glass and device readback when native Metal is available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_device_identity_spec.spl:115:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed before device dispatch for inactive 930 native Metal when available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
