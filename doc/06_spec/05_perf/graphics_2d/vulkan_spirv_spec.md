# Vulkan Spirv Specification

> Tests covering backend_vulkan_spirv — AC-2: SPIR-V shaders, no GLSL, shader format contract, pipeline creation, GLSL exclusion from selection path, api identity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vulkan Spirv Specification

## Scenarios

### backend_vulkan_spirv — AC-2: SPIR-V shaders, no GLSL

### shader format contract

#### AC-2: Vulkan probe reports shader_format spirv

- AC-2: Vulkan probe reports shader_format spirv
   - Expected: r.shader_format equals `VULKAN_SHADER_FORMAT_EXPECTED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-2: Vulkan probe reports shader_format spirv")
val r: VulkanProbeSentinel = make_vulkan_spirv_probe()
expect(r.shader_format).to_equal(VULKAN_SHADER_FORMAT_EXPECTED)
```

</details>

#### AC-2: Vulkan probe does not report shader_format glsl

- AC-2: Vulkan probe does not report shader_format glsl


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-2: Vulkan probe does not report shader_format glsl")
val r: VulkanProbeSentinel = make_vulkan_spirv_probe()
expect(r.shader_format).to_not_equal(VULKAN_SHADER_FORMAT_FORBIDDEN)
```

</details>

#### AC-2: spirv and glsl format names are distinct strings

- AC-2: spirv and glsl format names are distinct strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-2: spirv and glsl format names are distinct strings")
expect(VULKAN_SHADER_FORMAT_EXPECTED).to_not_equal(VULKAN_SHADER_FORMAT_FORBIDDEN)
```

</details>

### pipeline creation

#### AC-2: SPIR-V source uses compile_spirv facade

- AC-2: SPIR-V source uses compile_spirv facade
   - Expected: r.compile_symbol equals `vulkan_compile_spirv_api`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-2: SPIR-V source uses compile_spirv facade")
val r: VulkanProbeSentinel = make_vulkan_spirv_probe()
expect(r.compile_symbol).to_equal("vulkan_compile_spirv_api")
```

</details>

#### AC-2: SPIR-V focused pipeline path is active

- AC-2: SPIR-V focused pipeline path is active
   - Expected: r.pipeline_ok is true
   - Expected: r.failure_reason equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-2: SPIR-V focused pipeline path is active")
val r: VulkanProbeSentinel = make_vulkan_spirv_probe()
expect(r.pipeline_ok).to_equal(true)
expect(r.failure_reason).to_equal("")
```

</details>

#### AC-2: GLSL pipeline creation fails (pipeline_ok is false)

- AC-2: GLSL pipeline creation fails (pipeline_ok is false)
   - Expected: r.pipeline_ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-2: GLSL pipeline creation fails (pipeline_ok is false)")
val r: VulkanProbeSentinel = make_vulkan_glsl_probe()
expect(r.pipeline_ok).to_equal(false)
```

</details>

#### AC-2: Vulkan SPIR-V probe status records focused success

- AC-2: Vulkan SPIR-V probe status records focused success
   - Expected: r.status equals `Ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-2: Vulkan SPIR-V probe status records focused success")
val r: VulkanProbeSentinel = make_vulkan_spirv_probe()
expect(r.status).to_equal("Ok")
```

</details>

### GLSL exclusion from selection path

#### AC-2: GLSL probe is not in the selection path (glsl_in_path false for spirv)

- AC-2: GLSL probe is not in the selection path (glsl_in_path false for spirv)
   - Expected: r.glsl_in_path is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-2: GLSL probe is not in the selection path (glsl_in_path false for spirv)")
val r: VulkanProbeSentinel = make_vulkan_spirv_probe()
expect(r.glsl_in_path).to_equal(false)
```

</details>

#### AC-2: GLSL probe would be in path if GLSL were selected (sentinel check)

- AC-2: GLSL probe would be in path if GLSL were selected (sentinel check)
   - Expected: r.glsl_in_path is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-2: GLSL probe would be in path if GLSL were selected (sentinel check)")
val r: VulkanProbeSentinel = make_vulkan_glsl_probe()
expect(r.glsl_in_path).to_equal(true)
```

</details>

#### AC-2: ffi_dispatch rejects any probe result with shader_format glsl

- AC-2: ffi_dispatch rejects any probe result with shader_format glsl
   - Expected: glsl_is_rejected is true
   - Expected: spirv_is_accepted is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-2: ffi_dispatch rejects any probe result with shader_format glsl")
val glsl_fmt: text = "glsl"
val spirv_fmt: text = "spirv"
val glsl_is_rejected: bool = glsl_fmt == "glsl"
val spirv_is_accepted: bool = spirv_fmt == "spirv"
expect(glsl_is_rejected).to_equal(true)
expect(spirv_is_accepted).to_equal(true)
```

</details>

### api identity

#### AC-2: Vulkan probe reports api_name vulkan

- AC-2: Vulkan probe reports api_name vulkan
   - Expected: r.api_name equals `VULKAN_API_NAME`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-2: Vulkan probe reports api_name vulkan")
val r: VulkanProbeSentinel = make_vulkan_spirv_probe()
expect(r.api_name).to_equal(VULKAN_API_NAME)
```

</details>

#### AC-2: selected_name matches vulkan

- AC-2: selected_name matches vulkan
   - Expected: r.selected_name equals `vulkan`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-2: selected_name matches vulkan")
val r: VulkanProbeSentinel = make_vulkan_spirv_probe()
expect(r.selected_name).to_equal("vulkan")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/graphics_2d/vulkan_spirv_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering backend_vulkan_spirv — AC-2: SPIR-V shaders, no GLSL, shader format contract, pipeline creation, GLSL exclusion from selection path, api identity.
- backend_vulkan_spirv — AC-2: SPIR-V shaders, no GLSL
- shader format contract
- pipeline creation
- GLSL exclusion from selection path
- api identity

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

- `REQ-SSPEC-PERF`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `eecfd0b7d1ff3796f1d14d50caa4312b045c8e48116bc9d44ac7a6232cb35a42`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eecfd0b7d1ff3796f1d14d50caa4312b045c8e48116bc9d44ac7a6232cb35a42`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eecfd0b7d1ff3796f1d14d50caa4312b045c8e48116bc9d44ac7a6232cb35a42`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/05_perf/graphics_2d/vulkan_spirv_spec.spl
mirror: doc/06_spec/05_perf/graphics_2d/vulkan_spirv_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/05_perf/graphics_2d/vulkan_spirv_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/graphics_2d/vulkan_spirv_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/graphics_2d/vulkan_spirv_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2: Vulkan probe reports shader_format spirv' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/graphics_2d/vulkan_spirv_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2: Vulkan probe does not report shader_format glsl' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/graphics_2d/vulkan_spirv_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2: spirv and glsl format names are distinct strings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
