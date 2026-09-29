# webgpu_context_spec

> Purpose: This spec proves WebGPU Types.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# webgpu_context_spec

Purpose: This spec proves WebGPU Types.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/browser/webgpu_context_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves WebGPU Types.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### WebGPU Types

#### GPUAdapterInfo.software

#### returns the Simple software adapter

- returns the Simple software adapter
   - Expected: info.vendor equals `simple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEBGPUCONTEXT-001
step("returns the Simple software adapter")
val info = GPUAdapterInfo.software()
expect(info.vendor).to_equal("simple")
```

</details>

#### GPUDeviceLimits.defaults

#### has max_texture_dimension_2d == 8192

- has max_texture_dimension_2d == 8192
- has max_texture_dimension_2d == 8192
   - Expected: limits.max_texture_dimension_2d equals `8192`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("has max_texture_dimension_2d == 8192")
step("has max_texture_dimension_2d == 8192")
val limits = GPUDeviceLimits.defaults()
expect(limits.max_texture_dimension_2d).to_equal(8192)
```

</details>

#### GPURequestAdapterOptions.default_options

#### has force_fallback_adapter == false

- has force_fallback_adapter == false
- has force_fallback_adapter == false
   - Expected: opts.force_fallback_adapter is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("has force_fallback_adapter == false")
step("has force_fallback_adapter == false")
val opts = GPURequestAdapterOptions.default_options()
expect(opts.force_fallback_adapter).to_equal(false)
```

</details>

#### GPUDeviceDescriptor.create

#### has empty required_features

- has empty required_features
- has empty required_features
   - Expected: desc.required_features.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("has empty required_features")
step("has empty required_features")
val desc = GPUDeviceDescriptor.create()
expect(desc.required_features.len()).to_equal(0)
```

</details>

#### GPU_FEATURE_SHADER_F16

#### equals shader-f16

- equals shader-f16
- equals shader-f16
   - Expected: GPU_FEATURE_SHADER_F16 equals `shader-f16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("equals shader-f16")
step("equals shader-f16")
expect(GPU_FEATURE_SHADER_F16).to_equal("shader-f16")
```

</details>

#### GPU_POWER_HIGH

#### equals 1

- equals 1
- equals 1
   - Expected: GPU_POWER_HIGH equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("equals 1")
step("equals 1")
expect(GPU_POWER_HIGH).to_equal(1)
```

</details>

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

- `REQ-SSPEC-INTEGRATION`
- `REQ-WEBGPUCONTEXT-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ef8d6481261dfc0ca6f20feb82857fc6e1889a7aedbcf5e887f198f3de86087d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ef8d6481261dfc0ca6f20feb82857fc6e1889a7aedbcf5e887f198f3de86087d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ef8d6481261dfc0ca6f20feb82857fc6e1889a7aedbcf5e887f198f3de86087d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/browser/webgpu_context_spec.spl
mirror: doc/06_spec/integration/browser/webgpu_context_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/browser/webgpu_context_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/browser/webgpu_context_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/browser/webgpu_context_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/browser/webgpu_context_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the Simple software adapter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/browser/webgpu_context_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has max_texture_dimension_2d == 8192' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/browser/webgpu_context_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has force_fallback_adapter == false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
