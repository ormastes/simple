# Engine2d Wm Frame Executor Specification

> Tests covering Engine2D WM frame executor DrawIR target.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2d Wm Frame Executor Specification

## Scenarios

### Engine2D WM frame executor DrawIR target

#### should select scalar CPU when no host GPU or SIMD path is active

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should select scalar CPU when no host GPU or SIMD path is active
   - Expected: engine2d_wm_draw_ir_backend_target(false, "", false) equals `cpu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should select scalar CPU when no host GPU or SIMD path is active")
expect(engine2d_wm_draw_ir_backend_target(false, "", false)).to_equal("cpu")
```

</details>

#### should select CPU SIMD when the bare-metal SIMD capability is enabled

- should select CPU SIMD when the bare-metal SIMD capability is enabled
   - Expected: engine2d_wm_draw_ir_backend_target(false, "", true) equals `cpu_simd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should select CPU SIMD when the bare-metal SIMD capability is enabled")
expect(engine2d_wm_draw_ir_backend_target(false, "", true)).to_equal("cpu_simd")
```

</details>

#### should retain the negotiated Vulkan or Metal host backend

- should retain the negotiated Vulkan or Metal host backend
   - Expected: engine2d_wm_draw_ir_backend_target(true, "vulkan", false) equals `vulkan`
   - Expected: engine2d_wm_draw_ir_backend_target(true, "metal", true) equals `metal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should retain the negotiated Vulkan or Metal host backend")
expect(engine2d_wm_draw_ir_backend_target(true, "vulkan", false)).to_equal("vulkan")
expect(engine2d_wm_draw_ir_backend_target(true, "metal", true)).to_equal("metal")
```

</details>

#### should fall back when the host backend is inactive or empty

- should fall back when the host backend is inactive or empty
   - Expected: engine2d_wm_draw_ir_backend_target(false, "vulkan", true) equals `cpu_simd`
   - Expected: engine2d_wm_draw_ir_backend_target(true, "", false) equals `cpu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should fall back when the host backend is inactive or empty")
expect(engine2d_wm_draw_ir_backend_target(false, "vulkan", true)).to_equal("cpu_simd")
expect(engine2d_wm_draw_ir_backend_target(true, "", false)).to_equal("cpu")
```

</details>

#### should recompose only when the attempted host material target differs from local fallback

- should recompose only when the attempted host material target differs from local fallback
   - Expected: engine2d_wm_draw_ir_local_recompose_required("cpu", "cpu") is false
   - Expected: engine2d_wm_draw_ir_local_recompose_required("cpu_simd", "cpu_simd") is false
   - Expected: engine2d_wm_draw_ir_local_recompose_required("metal", "cpu") is true
   - Expected: engine2d_wm_draw_ir_local_recompose_required("vulkan", "cpu_simd") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should recompose only when the attempted host material target differs from local fallback")
expect(engine2d_wm_draw_ir_local_recompose_required("cpu", "cpu")).to_equal(false)
expect(engine2d_wm_draw_ir_local_recompose_required("cpu_simd", "cpu_simd")).to_equal(false)
expect(engine2d_wm_draw_ir_local_recompose_required("metal", "cpu")).to_equal(true)
expect(engine2d_wm_draw_ir_local_recompose_required("vulkan", "cpu_simd")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/engine2d_wm_frame_executor_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Engine2D WM frame executor DrawIR target.
- Engine2D WM frame executor DrawIR target

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `242be9383d9f26d425ea90137e29a3c2c8568862ed747c630672dab62808aae0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `242be9383d9f26d425ea90137e29a3c2c8568862ed747c630672dab62808aae0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `242be9383d9f26d425ea90137e29a3c2c8568862ed747c630672dab62808aae0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/os/compositor/engine2d_wm_frame_executor_spec.spl
mirror: doc/06_spec/01_unit/os/compositor/engine2d_wm_frame_executor_spec.md (current)
findings: 10 blockers: 0
  narrative=100 structure=75 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/compositor/engine2d_wm_frame_executor_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/compositor/engine2d_wm_frame_executor_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/compositor/engine2d_wm_frame_executor_spec.spl:17:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should select scalar CPU when no host GPU or SIMD path is active' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/compositor/engine2d_wm_frame_executor_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should select scalar CPU when no host GPU or SIMD path is active' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/engine2d_wm_frame_executor_spec.spl:22:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should select CPU SIMD when the bare-metal SIMD capability is enabled' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/compositor/engine2d_wm_frame_executor_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should select CPU SIMD when the bare-metal SIMD capability is enabled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/engine2d_wm_frame_executor_spec.spl:27:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain the negotiated Vulkan or Metal host backend' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/compositor/engine2d_wm_frame_executor_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should retain the negotiated Vulkan or Metal host backend' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/engine2d_wm_frame_executor_spec.spl:33:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should fall back when the host backend is inactive or empty' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/compositor/engine2d_wm_frame_executor_spec.spl:39:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should recompose only when the attempted host material target differs from local fallback' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
