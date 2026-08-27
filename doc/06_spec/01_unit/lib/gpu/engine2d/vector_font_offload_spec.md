# Vector Font Offload Specification

> Tests covering Engine2D vector font offload evidence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vector Font Offload Specification

## Scenarios

### Engine2D vector font offload evidence

#### marks CUDA vector font evidence production ready only after GPU glyph pixels return

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- marks CUDA vector font evidence production ready only after GPU glyph pixels return
   - Expected: evidence.generated_ready is true
   - Expected: evidence.generated.generated_operation equals `copy`
   - Expected: evidence.cpu_preprocess_required is true
   - Expected: evidence.gpu_glyph_returned is true
   - Expected: evidence.production_ready is true
   - Expected: evidence.status_code equals `gpu-glyph-returned`
   - Expected: evidence.reason equals `cuda-vector-font-glyph-pixels-returned`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("marks CUDA vector font evidence production ready only after GPU glyph pixels return")
val evidence = vector_font_offload_evidence(
    "cuda", 48, 24, true, true, 4096,
    accel(1, 1, 0, 0, 1, 128, "cuda-vector-font-glyph-pixels-returned")
)

expect(evidence.generated_ready).to_equal(true)
expect(evidence.generated.generated_operation).to_equal("copy")
expect(evidence.cpu_preprocess_required).to_equal(true)
expect(evidence.gpu_glyph_returned).to_equal(true)
expect(evidence.production_ready).to_equal(true)
expect(evidence.status_code).to_equal("gpu-glyph-returned")
expect(evidence.reason).to_equal("cuda-vector-font-glyph-pixels-returned")
expect(evidence.diagnostic_text()).to_contain("family=vector_font")
```

</details>

#### keeps generated-ready OpenCL evidence separate from missing glyph readback

- keeps generated-ready OpenCL evidence separate from missing glyph readback
   - Expected: evidence.generated_ready is true
   - Expected: evidence.gpu_glyph_returned is false
   - Expected: evidence.production_ready is false
   - Expected: evidence.status_code equals `gpu-proof-with-cpu-glyph`
   - Expected: evidence.reason equals `opencl-vector-font-proof-matched-cpu-with-cpu-glyph-return`
   - Expected: evidence.generated.launch_api equals `clEnqueueNDRangeKernel`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps generated-ready OpenCL evidence separate from missing glyph readback")
val evidence = vector_font_offload_evidence(
    "opencl", 48, 24, true, true, 8192,
    accel(1, 0, 1, 1, 0, 0, "opencl-vector-font-proof-matched-cpu-with-cpu-glyph-return")
)

expect(evidence.generated_ready).to_equal(true)
expect(evidence.gpu_glyph_returned).to_equal(false)
expect(evidence.production_ready).to_equal(false)
expect(evidence.status_code).to_equal("gpu-proof-with-cpu-glyph")
expect(evidence.reason).to_equal("opencl-vector-font-proof-matched-cpu-with-cpu-glyph-return")
expect(evidence.generated.launch_api).to_equal("clEnqueueNDRangeKernel")
```

</details>

#### fails closed when the generated backend runtime is unavailable

- fails closed when the generated backend runtime is unavailable
   - Expected: evidence.generated_ready is false
   - Expected: evidence.production_ready is false
   - Expected: evidence.status_code equals `cuda-runtime-unavailable`
   - Expected: evidence.reason equals `runtime-not-ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails closed when the generated backend runtime is unavailable")
val evidence = vector_font_offload_evidence(
    "cuda", 48, 24, false, false, 4096,
    accel(1, 0, 0, 1, 0, 0, "production-gpu-dispatch-not-wired")
)

expect(evidence.generated_ready).to_equal(false)
expect(evidence.production_ready).to_equal(false)
expect(evidence.status_code).to_equal("cuda-runtime-unavailable")
expect(evidence.reason).to_equal("runtime-not-ready")
```

</details>

#### reports CPU fallback as an incomplete vector font offload state

- reports CPU fallback as an incomplete vector font offload state
   - Expected: evidence.generated_ready is true
   - Expected: evidence.gpu_glyph_returned is false
   - Expected: evidence.production_ready is false
   - Expected: evidence.status_code equals `cpu-fallback`
   - Expected: evidence.reason equals `production-gpu-dispatch-not-wired`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports CPU fallback as an incomplete vector font offload state")
val evidence = vector_font_offload_evidence(
    "cuda", 48, 24, true, true, 4096,
    accel(1, 0, 0, 1, 0, 0, "production-gpu-dispatch-not-wired")
)

expect(evidence.generated_ready).to_equal(true)
expect(evidence.gpu_glyph_returned).to_equal(false)
expect(evidence.production_ready).to_equal(false)
expect(evidence.status_code).to_equal("cpu-fallback")
expect(evidence.reason).to_equal("production-gpu-dispatch-not-wired")
```

</details>

#### uses the Engine2D font offload order before producing vector evidence

- uses the Engine2D font offload order before producing vector evidence
   - Expected: evidence.backend_name equals `rocm`
   - Expected: evidence.generated.backend_name equals `rocm`
   - Expected: evidence.generated_ready is true
   - Expected: fallback.backend_name equals `cpu`
   - Expected: fallback.generated_ready is true
   - Expected: fallback.status_code equals `no-preferred-font-backend`
   - Expected: fallback.reason equals `no-preferred-font-backend-candidate`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("uses the Engine2D font offload order before producing vector evidence")
val evidence = vector_font_preferred_offload_evidence(
    ["vulkan", "amd-hip", "cpu"],
    48, 24, true, true, 4096,
    accel(1, 0, 0, 1, 0, 0, "preferred-vector-font-offload-cpu-glyph")
)
val fallback = vector_font_preferred_offload_evidence(
    ["unknown"], 48, 24, true, true, 4096,
    accel(1, 0, 0, 1, 0, 0, "no-known-vector-font-backend")
)

expect(evidence.backend_name).to_equal("rocm")
expect(evidence.generated.backend_name).to_equal("rocm")
expect(evidence.generated_ready).to_equal(true)
expect(fallback.backend_name).to_equal("cpu")
expect(fallback.generated_ready).to_equal(true)
expect(fallback.status_code).to_equal("no-preferred-font-backend")
expect(fallback.reason).to_equal("no-preferred-font-backend-candidate")
```

</details>

#### marks vector font glyph readback ready only when returned pixels match checksum

- marks vector font glyph readback ready only when returned pixels match checksum
   - Expected: evidence.execution.expected_checksum equals `checksum`
   - Expected: evidence.execution.actual_checksum equals `checksum`
   - Expected: evidence.gpu_glyph_returned is true
   - Expected: evidence.gpu_glyph_readback_matched is true
   - Expected: evidence.production_ready is true
   - Expected: evidence.status_code equals `vector-font-glyph-readback-matched`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("marks vector font glyph readback ready only when returned pixels match checksum")
val pixels = [0u8, 24u8, 255u8, 6u8]
val checksum = vector_font_glyph_pixels_checksum(pixels)
val evidence = vector_font_glyph_readback_evidence(
    "cuda", 4, 1, 4096, 7, 11, true, true, true,
    accel(1, 1, 0, 0, 1, 4, "cuda-vector-font-glyph-pixels-returned"),
    pixels, checksum
)

expect(checksum).to_be_greater_than(0)
expect(evidence.execution.expected_checksum).to_equal(checksum)
expect(evidence.execution.actual_checksum).to_equal(checksum)
expect(evidence.gpu_glyph_returned).to_equal(true)
expect(evidence.gpu_glyph_readback_matched).to_equal(true)
expect(evidence.production_ready).to_equal(true)
expect(evidence.status_code).to_equal("vector-font-glyph-readback-matched")
expect(evidence.diagnostic_text()).to_contain("gpu_glyph_readback_matched=true")
```

</details>

#### uses the Engine2D font offload order before vector glyph readback proof

- uses the Engine2D font offload order before vector glyph readback proof
   - Expected: evidence.backend_name equals `rocm`
   - Expected: evidence.submit.request.plan.compute_target equals `hip`
   - Expected: evidence.execution.device_executed is true
   - Expected: evidence.production_ready is true
   - Expected: evidence.status_code equals `vector-font-glyph-readback-matched`
   - Expected: fallback.backend_name equals `cpu`
   - Expected: fallback.execution.device_executed is false
   - Expected: fallback.execution.expected_checksum equals `0`
   - Expected: fallback.production_ready is false
   - Expected: fallback.status_code equals `vector-font-glyph-no-preferred-font-backend`
   - Expected: fallback.reason equals `no-preferred-font-backend-candidate`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("uses the Engine2D font offload order before vector glyph readback proof")
val pixels = [0u8, 24u8, 255u8, 6u8]
val checksum = vector_font_glyph_pixels_checksum(pixels)
val evidence = vector_font_preferred_glyph_readback_evidence(
    ["vulkan", "amd-hip", "cpu"],
    4, 1, 4096, 7, 11, true, true, true,
    accel(1, 0, 0, 0, 1, 4, "rocm-vector-font-glyph-pixels-returned"),
    pixels, checksum
)
val fallback = vector_font_preferred_glyph_readback_evidence(
    ["unknown"],
    4, 1, 4096, 7, 11, true, true, true,
    accel(1, 0, 0, 1, 1, 4, "no-known-vector-font-readback-backend"),
    pixels, checksum
)

expect(evidence.backend_name).to_equal("rocm")
expect(evidence.submit.request.plan.compute_target).to_equal("hip")
expect(evidence.execution.device_executed).to_equal(true)
expect(evidence.production_ready).to_equal(true)
expect(evidence.status_code).to_equal("vector-font-glyph-readback-matched")
expect(fallback.backend_name).to_equal("cpu")
expect(fallback.execution.device_executed).to_equal(false)
expect(fallback.execution.expected_checksum).to_equal(0)
expect(fallback.production_ready).to_equal(false)
expect(fallback.status_code).to_equal("vector-font-glyph-no-preferred-font-backend")
expect(fallback.reason).to_equal("no-preferred-font-backend-candidate")
```

</details>

#### keeps vector font glyph readback incomplete without GPU returned glyph evidence

- keeps vector font glyph readback incomplete without GPU returned glyph evidence
   - Expected: evidence.execution.device_executed is true
   - Expected: evidence.gpu_glyph_returned is false
   - Expected: evidence.gpu_glyph_readback_matched is false
   - Expected: evidence.production_ready is false
   - Expected: evidence.status_code equals `vector-font-glyph-return-missing`
   - Expected: evidence.reason equals `vector-font-gpu-glyph-return-missing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps vector font glyph readback incomplete without GPU returned glyph evidence")
val pixels = [0u8, 24u8, 255u8, 6u8]
val checksum = vector_font_glyph_pixels_checksum(pixels)
val evidence = vector_font_glyph_readback_evidence(
    "cuda", 4, 1, 4096, 7, 11, true, true, true,
    accel(1, 1, 0, 0, 0, 0, "cuda-vector-font-glyph-pixels-missing"),
    pixels, checksum
)

expect(evidence.execution.device_executed).to_equal(true)
expect(evidence.gpu_glyph_returned).to_equal(false)
expect(evidence.gpu_glyph_readback_matched).to_equal(false)
expect(evidence.production_ready).to_equal(false)
expect(evidence.status_code).to_equal("vector-font-glyph-return-missing")
expect(evidence.reason).to_equal("vector-font-gpu-glyph-return-missing")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/vector_font_offload_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Engine2D vector font offload evidence.
- Engine2D vector font offload evidence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `cd7c1843e74e60112a2a284caeb300e2a0f54bb207ee8595d655b0f13a49f840`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cd7c1843e74e60112a2a284caeb300e2a0f54bb207ee8595d655b0f13a49f840`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cd7c1843e74e60112a2a284caeb300e2a0f54bb207ee8595d655b0f13a49f840`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **95/100**; effective score: **95/100**; blockers: **0**.

SSpec documentization score: 95/100
source: test/01_unit/lib/gpu/engine2d/vector_font_offload_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu/engine2d/vector_font_offload_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu/engine2d/vector_font_offload_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu/engine2d/vector_font_offload_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu/engine2d/vector_font_offload_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
<!-- sspec-maintain:scorecard:end -->
