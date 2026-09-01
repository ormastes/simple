# Webgpu Real Specification

> Tests covering backend_webgpu — AC-5: real adapter enumeration, no silent fallback, WebGPU probe identity, adapter enumeration, no silent CPU fallback.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Webgpu Real Specification

## Scenarios

### backend_webgpu — AC-5: real adapter enumeration, no silent fallback

### WebGPU probe identity

#### AC-5: WebGPU probe reports backend name webgpu

- verify WebGPU probe reports backend name webgpu
   - Expected: r.backend equals `WEBGPU_BACKEND_NAME`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-WEBGPU-REAL
step("verify WebGPU probe reports backend name webgpu")
val r: WebGpuProbeSentinel = make_webgpu_real_probe()
expect(r.backend).to_equal(WEBGPU_BACKEND_NAME)
```

</details>

#### AC-5: WebGPU probe reports shader_format wgsl

- verify WebGPU probe reports shader_format wgsl
   - Expected: r.shader_format equals `WEBGPU_SHADER_FORMAT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-WEBGPU-REAL
step("verify WebGPU probe reports shader_format wgsl")
val r: WebGpuProbeSentinel = make_webgpu_real_probe()
expect(r.shader_format).to_equal(WEBGPU_SHADER_FORMAT)
```

</details>

#### AC-5: WebGPU probe reports api_name wgpu

- verify WebGPU probe reports api_name wgpu
   - Expected: r.api_name equals `WEBGPU_API_NAME`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-WEBGPU-REAL
step("verify WebGPU probe reports api_name wgpu")
val r: WebGpuProbeSentinel = make_webgpu_real_probe()
expect(r.api_name).to_equal(WEBGPU_API_NAME)
```

</details>

#### AC-5: WebGPU status is Ok when adapter is found

- verify WebGPU status is Ok when adapter is found
   - Expected: r.status equals `Ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-WEBGPU-REAL
step("verify WebGPU status is Ok when adapter is found")
val r: WebGpuProbeSentinel = make_webgpu_real_probe()
expect(r.status).to_equal("Ok")
```

</details>

### adapter enumeration

#### AC-5: adapter_count is greater than zero when WebGPU is available

- verify adapter_count is greater than zero when WebGPU is available
   - Expected: r.adapter_count > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-WEBGPU-REAL
step("verify adapter_count is greater than zero when WebGPU is available")
val r: WebGpuProbeSentinel = make_webgpu_real_probe()
expect(r.adapter_count > 0).to_equal(true)
```

</details>

#### AC-5: selected_adapter is non-empty when WebGPU is available

- verify selected_adapter is non-empty when WebGPU is available
   - Expected: r.selected_adapter equals `DiscreteGpu(NVIDIA GeForce RTX 3080)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-WEBGPU-REAL
step("verify selected_adapter is non-empty when WebGPU is available")
val r: WebGpuProbeSentinel = make_webgpu_real_probe()
expect(r.selected_adapter).to_equal("DiscreteGpu(NVIDIA GeForce RTX 3080)")
```

</details>

#### AC-5: adapter_count is zero when no GPU hardware is present

- verify adapter_count is zero when no GPU hardware is present
   - Expected: r.adapter_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-WEBGPU-REAL
step("verify adapter_count is zero when no GPU hardware is present")
val r: WebGpuProbeSentinel = make_webgpu_no_adapter()
expect(r.adapter_count).to_equal(0)
```

</details>

#### AC-5: status is Failed (not Fallback) when no adapters are enumerated

- verify status is Failed (not Fallback) when no adapters are enumerated
   - Expected: r.status equals `Failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-WEBGPU-REAL
step("verify status is Failed (not Fallback) when no adapters are enumerated")
val r: WebGpuProbeSentinel = make_webgpu_no_adapter()
expect(r.status).to_equal("Failed")
```

</details>

### no silent CPU fallback

#### AC-5: fell_through_to_cpu is false when real WebGPU is selected

- verify fell_through_to_cpu is false when real WebGPU is selected
   - Expected: r.fell_through_to_cpu is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-WEBGPU-REAL
step("verify fell_through_to_cpu is false when real WebGPU is selected")
val r: WebGpuProbeSentinel = make_webgpu_real_probe()
expect(r.fell_through_to_cpu).to_equal(false)
```

</details>

#### AC-5: silent fallback probe has fell_through_to_cpu true (sentinel for what is forbidden)

- verify silent fallback probe has fell_through_to_cpu true (sentinel for what is forbidden)
   - Expected: r.fell_through_to_cpu is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-WEBGPU-REAL
step("verify silent fallback probe has fell_through_to_cpu true (sentinel for what is forbidden)")
val r: WebGpuProbeSentinel = make_webgpu_silent_fallback()
expect(r.fell_through_to_cpu).to_equal(true)
```

</details>

#### AC-5: silent fallback status is Fallback (strict mode must reject this)

- verify silent fallback status is Fallback (strict mode must reject this)
   - Expected: r.status equals `Fallback`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-WEBGPU-REAL
step("verify silent fallback status is Fallback (strict mode must reject this)")
val r: WebGpuProbeSentinel = make_webgpu_silent_fallback()
expect(r.status).to_equal("Fallback")
```

</details>

#### AC-5: real WebGPU probe fallback_reason is empty

- verify real WebGPU probe fallback_reason is empty
   - Expected: r.fallback_reason equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-WEBGPU-REAL
step("verify real WebGPU probe fallback_reason is empty")
val r: WebGpuProbeSentinel = make_webgpu_real_probe()
expect(r.fallback_reason).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Performance |
| Status | Active |
| Source | `test/perf/graphics_2d/webgpu_real_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering backend_webgpu — AC-5: real adapter enumeration, no silent fallback, WebGPU probe identity, adapter enumeration, no silent CPU fallback.
- backend_webgpu — AC-5: real adapter enumeration, no silent fallback
- WebGPU probe identity
- adapter enumeration
- no silent CPU fallback

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

- `REQ-PERF-WEBGPU-REAL`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a735e513784925106c1290a0382977167e56aff3b0444d561dc845fee64987b5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a735e513784925106c1290a0382977167e56aff3b0444d561dc845fee64987b5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a735e513784925106c1290a0382977167e56aff3b0444d561dc845fee64987b5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/perf/graphics_2d/webgpu_real_spec.spl
mirror: doc/06_spec/perf/graphics_2d/webgpu_real_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=60
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/perf/graphics_2d/webgpu_real_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/perf/graphics_2d/webgpu_real_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/perf/graphics_2d/webgpu_real_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/perf/graphics_2d/webgpu_real_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/perf/graphics_2d/webgpu_real_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: WebGPU probe reports backend name webgpu' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/perf/graphics_2d/webgpu_real_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: WebGPU probe reports shader_format wgsl' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/perf/graphics_2d/webgpu_real_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: WebGPU probe reports api_name wgpu' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
