# Vector Font Offload Specification

> 1. accel native

<!-- sdn-diagram:id=vector_font_offload_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vector_font_offload_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vector_font_offload_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vector_font_offload_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vector Font Offload Specification

## Scenarios

### Engine2D vector font offload evidence

#### treats native backend vector font proof as GPU proof before CPU fallback

1. accel native
   - Expected: evidence.generated_ready is true
   - Expected: evidence.gpu_glyph_returned is false
   - Expected: evidence.production_ready is false
   - Expected: evidence.status_code equals `gpu-proof-with-cpu-glyph`
   - Expected: evidence.reason equals `metal-vector-font-proof-matched-cpu-with-cpu-glyph-return`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = vector_font_offload_evidence(
    "metal", 48, 24, true, true, 4096,
    accel_native(1, 1, 0, 0, 0, 0, 1, 0, 0, "metal-vector-font-proof-matched-cpu-with-cpu-glyph-return")
)

expect(evidence.generated_ready).to_equal(true)
expect(evidence.gpu_glyph_returned).to_equal(false)
expect(evidence.production_ready).to_equal(false)
expect(evidence.status_code).to_equal("gpu-proof-with-cpu-glyph")
expect(evidence.reason).to_equal("metal-vector-font-proof-matched-cpu-with-cpu-glyph-return")
```

</details>

#### marks CUDA vector font evidence production ready only after GPU glyph pixels return

1. accel
   - Expected: evidence.generated_ready is true
   - Expected: evidence.generated.generated_operation equals `glyph_raster`
   - Expected: evidence.cpu_preprocess_required is true
   - Expected: evidence.gpu_glyph_returned is true
   - Expected: evidence.production_ready is true
   - Expected: evidence.status_code equals `gpu-glyph-returned`
   - Expected: evidence.reason equals `cuda-vector-font-glyph-pixels-returned`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = vector_font_offload_evidence(
    "cuda", 48, 24, true, true, 4096,
    accel(1, 1, 0, 0, 1, 128, "cuda-vector-font-glyph-pixels-returned")
)

expect(evidence.generated_ready).to_equal(true)
expect(evidence.generated.generated_operation).to_equal("glyph_raster")
expect(evidence.cpu_preprocess_required).to_equal(true)
expect(evidence.gpu_glyph_returned).to_equal(true)
expect(evidence.production_ready).to_equal(true)
expect(evidence.status_code).to_equal("gpu-glyph-returned")
expect(evidence.reason).to_equal("cuda-vector-font-glyph-pixels-returned")
expect(evidence.diagnostic_text()).to_contain("family=vector_font")
```

</details>

#### keeps generated-ready OpenCL evidence separate from missing glyph readback

1. accel
   - Expected: evidence.generated_ready is true
   - Expected: evidence.gpu_glyph_returned is false
   - Expected: evidence.production_ready is false
   - Expected: evidence.status_code equals `gpu-proof-with-cpu-glyph`
   - Expected: evidence.reason equals `opencl-vector-font-proof-matched-cpu-with-cpu-glyph-return`
   - Expected: evidence.generated.launch_api equals `clEnqueueNDRangeKernel`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. accel
   - Expected: evidence.generated_ready is false
   - Expected: evidence.production_ready is false
   - Expected: evidence.status_code equals `cuda-runtime-unavailable`
   - Expected: evidence.reason equals `runtime-not-ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. accel
   - Expected: evidence.generated_ready is true
   - Expected: evidence.gpu_glyph_returned is false
   - Expected: evidence.production_ready is false
   - Expected: evidence.status_code equals `cpu-fallback`
   - Expected: evidence.reason equals `production-gpu-dispatch-not-wired`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/vector_font_offload_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine2D vector font offload evidence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
