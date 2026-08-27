# Metal Smoke Specification

> Tests covering backend_metal — AC-4: Metal macOS-gated, Metal probe identity, MTLComputePipelineState, correctness via sync_readback.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Metal Smoke Specification

## Scenarios

### backend_metal — AC-4: Metal macOS-gated

### Metal probe identity

#### AC-4: Metal probe reports backend name metal

- AC-4: Metal probe reports backend name metal
   - Expected: s.backend equals `METAL_BACKEND_NAME`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-4: Metal probe reports backend name metal")
val s: MetalSmokeSentinel = make_metal_smoke_ok()
expect(s.backend).to_equal(METAL_BACKEND_NAME)
```

</details>

#### AC-4: Metal probe reports shader_format msl

- AC-4: Metal probe reports shader_format msl
   - Expected: s.shader_format equals `METAL_SHADER_FORMAT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-4: Metal probe reports shader_format msl")
val s: MetalSmokeSentinel = make_metal_smoke_ok()
expect(s.shader_format).to_equal(METAL_SHADER_FORMAT)
```

</details>

#### AC-4: Metal probe reports api_name metal

- AC-4: Metal probe reports api_name metal
   - Expected: s.api_name equals `METAL_API_NAME`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-4: Metal probe reports api_name metal")
val s: MetalSmokeSentinel = make_metal_smoke_ok()
expect(s.api_name).to_equal(METAL_API_NAME)
```

</details>

#### AC-4: Metal status is Ok when available

- AC-4: Metal status is Ok when available
   - Expected: s.status equals `Ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-4: Metal status is Ok when available")
val s: MetalSmokeSentinel = make_metal_smoke_ok()
expect(s.status).to_equal("Ok")
```

</details>

#### AC-4: Metal status is Failed when not on macOS

- AC-4: Metal status is Failed when not on macOS
   - Expected: s.status equals `Failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-4: Metal status is Failed when not on macOS")
val s: MetalSmokeSentinel = make_metal_unavailable()
expect(s.status).to_equal("Failed")
```

</details>

### MTLComputePipelineState

#### AC-4: pipeline_state_ok is true when Metal is available

- AC-4: pipeline_state_ok is true when Metal is available
   - Expected: s.pipeline_state_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-4: pipeline_state_ok is true when Metal is available")
val s: MetalSmokeSentinel = make_metal_smoke_ok()
expect(s.pipeline_state_ok).to_equal(true)
```

</details>

#### AC-4: dispatch_ok is true when pipeline state is ready

- AC-4: dispatch_ok is true when pipeline state is ready
   - Expected: s.dispatch_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-4: dispatch_ok is true when pipeline state is ready")
val s: MetalSmokeSentinel = make_metal_smoke_ok()
expect(s.dispatch_ok).to_equal(true)
```

</details>

#### AC-4: pipeline_state_ok is false when Metal is unavailable

- AC-4: pipeline_state_ok is false when Metal is unavailable
   - Expected: s.pipeline_state_ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-4: pipeline_state_ok is false when Metal is unavailable")
val s: MetalSmokeSentinel = make_metal_unavailable()
expect(s.pipeline_state_ok).to_equal(false)
```

</details>

### correctness via sync_readback

#### AC-4: sync_readback completes when Metal is available

- AC-4: sync_readback completes when Metal is available
   - Expected: s.readback_completed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-4: sync_readback completes when Metal is available")
val s: MetalSmokeSentinel = make_metal_smoke_ok()
expect(s.readback_completed).to_equal(true)
```

</details>

#### AC-4: Metal pixel hash matches CPU reference hash

- AC-4: Metal pixel hash matches CPU reference hash
   - Expected: metal_hashes_match(s) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-4: Metal pixel hash matches CPU reference hash")
val s: MetalSmokeSentinel = make_metal_smoke_ok()
expect(metal_hashes_match(s)).to_equal(true)
```

</details>

#### AC-4: metal_pixel_hash equals cpu_pixel_hash exactly

- AC-4: metal_pixel_hash equals cpu_pixel_hash exactly
   - Expected: s.metal_pixel_hash equals `s.cpu_pixel_hash`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-4: metal_pixel_hash equals cpu_pixel_hash exactly")
val s: MetalSmokeSentinel = make_metal_smoke_ok()
expect(s.metal_pixel_hash).to_equal(s.cpu_pixel_hash)
```

</details>

#### AC-4: readback is not completed when Metal is unavailable

- AC-4: readback is not completed when Metal is unavailable
   - Expected: s.readback_completed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-4: readback is not completed when Metal is unavailable")
val s: MetalSmokeSentinel = make_metal_unavailable()
expect(s.readback_completed).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/graphics_2d/metal_smoke_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering backend_metal — AC-4: Metal macOS-gated, Metal probe identity, MTLComputePipelineState, correctness via sync_readback.
- backend_metal — AC-4: Metal macOS-gated
- Metal probe identity
- MTLComputePipelineState
- correctness via sync_readback

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

- Canonical SPipe generation for source `9cb3a5373b7733d58bb6ec263078ed8aa49f2bc97a1df8f5334bf45df1a8310e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9cb3a5373b7733d58bb6ec263078ed8aa49f2bc97a1df8f5334bf45df1a8310e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9cb3a5373b7733d58bb6ec263078ed8aa49f2bc97a1df8f5334bf45df1a8310e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/05_perf/graphics_2d/metal_smoke_spec.spl
mirror: doc/06_spec/05_perf/graphics_2d/metal_smoke_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/05_perf/graphics_2d/metal_smoke_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/graphics_2d/metal_smoke_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/graphics_2d/metal_smoke_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-4: Metal probe reports backend name metal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/graphics_2d/metal_smoke_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-4: Metal probe reports shader_format msl' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/graphics_2d/metal_smoke_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-4: Metal probe reports api_name metal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
