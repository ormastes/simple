# backend_qualcomm_spec

> Qualcomm Adreno Backend Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# backend_qualcomm_spec

Qualcomm Adreno Backend Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/backend_qualcomm_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Qualcomm Adreno Backend Specification

@tag: gpu, engine2d, qualcomm, adreno, vulkan
NO COVERAGE CLAIMED. Stream F4 (2026-08-09) removed the
`@cover src/lib/gc_async_mut/gpu/engine2d/backend_qualcomm.spl 80%` claim that stood here: all 12 `it` bodies are the single gate assertion
`expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")`,
which asserts only that the gate is shut. The file never references
QualcommBackend, so it covered 0% of it, not 80%.
NOTE for whoever picks this up: the subject is real (273 lines) and much of
it is testable WITHOUT a Snapdragon -- `qualcomm_supports_target`,
`qualcomm_vulkan_profile_key`, `qualcomm_preferred_backend_for_target`,
`qualcomm_preferred_workgroup_size`, `qualcomm_subgroup_size` and
`create_for_target` are pure and host-independent. Only the actual
render/present path needs Adreno hardware, which this host lacks.
See doc/08_tracking/bug/gated_specs_are_tautology_shells_2026-08-09.md
and doc/08_tracking/bug/gc_async_mut_gpu_ffi_facades_are_dangling_2026-08-09.md.

Verifies the Qualcomm Adreno backend which delegates to VulkanBackend
with Adreno-specific detection and tuning. Covers AC-5.

## Scenarios

### QualcommBackend

### is_adreno_gpu

#### AC-5: detects Adreno via Vulkan vendorID 0x5143

- AC-5: detects Adreno via Vulkan vendorID 0x5143
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: detects Adreno via Vulkan vendorID 0x5143")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-5: returns false for non-Qualcomm vendor

- AC-5: returns false for non-Qualcomm vendor
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: returns false for non-Qualcomm vendor")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

### create

#### AC-5: creates a QualcommBackend wrapping VulkanBackend

- AC-5: creates a QualcommBackend wrapping VulkanBackend
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: creates a QualcommBackend wrapping VulkanBackend")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-5: init delegates to VulkanBackend.init

- AC-5: init delegates to VulkanBackend.init
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: init delegates to VulkanBackend.init")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

### RenderBackend trait

#### AC-5: clear delegates to Vulkan compute shader

- AC-5: clear delegates to Vulkan compute shader
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: clear delegates to Vulkan compute shader")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-5: draw_rect_filled delegates to Vulkan

- AC-5: draw_rect_filled delegates to Vulkan
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: draw_rect_filled delegates to Vulkan")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-5: width and height match init dimensions

- AC-5: width and height match init dimensions
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: width and height match init dimensions")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-5: shutdown releases Vulkan resources

- AC-5: shutdown releases Vulkan resources
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: shutdown releases Vulkan resources")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

### Adreno tuning

#### AC-5: preferred workgroup size for Adreno

- AC-5: preferred workgroup size for Adreno
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: preferred workgroup size for Adreno")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-5: subgroup size for Adreno GPUs

- AC-5: subgroup size for Adreno GPUs
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: subgroup size for Adreno GPUs")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

### platform support

#### AC-7: Qualcomm on Linux arm64 via Turnip driver

- AC-7: Qualcomm on Linux arm64 via Turnip driver
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-7: Qualcomm on Linux arm64 via Turnip driver")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-5: Qualcomm delegates to Vulkan (no separate FFI)

- AC-5: Qualcomm delegates to Vulkan (no separate FFI)
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: Qualcomm delegates to Vulkan (no separate FFI)")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `ba797512fedea34ebc615a4b3c63f0fdd35d0852eaa57b96e2d4882e1dc841d9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ba797512fedea34ebc615a4b3c63f0fdd35d0852eaa57b96e2d4882e1dc841d9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ba797512fedea34ebc615a4b3c63f0fdd35d0852eaa57b96e2d4882e1dc841d9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gpu/engine2d/backend_qualcomm_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu/engine2d/backend_qualcomm_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu/engine2d/backend_qualcomm_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu/engine2d/backend_qualcomm_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu/engine2d/backend_qualcomm_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: detects Adreno via Vulkan vendorID 0x5143' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/backend_qualcomm_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: returns false for non-Qualcomm vendor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/backend_qualcomm_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: creates a QualcommBackend wrapping VulkanBackend' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
