# Vector Font Offload Specification

> <details>

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
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vector Font Offload Specification

## Scenarios

### Engine2D vector font offload evidence

#### marks CUDA vector font evidence production ready only after GPU glyph pixels return

- accel
   - Expected: evidence.generated_ready is true
   - Expected: evidence.generated.generated_operation equals `copy`
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

- accel
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

- accel
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

- accel
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

#### uses the Engine2D font offload order before producing vector evidence

- accel
- accel
   - Expected: evidence.backend_name equals `rocm`
   - Expected: evidence.generated.backend_name equals `rocm`
   - Expected: evidence.generated_ready is true
   - Expected: fallback.backend_name equals `cpu`
   - Expected: fallback.generated_ready is true
   - Expected: fallback.status_code equals `no-preferred-font-backend`
   - Expected: fallback.reason equals `no-preferred-font-backend-candidate`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- accel
   - Expected: evidence.execution.expected_checksum equals `checksum`
   - Expected: evidence.execution.actual_checksum equals `checksum`
   - Expected: evidence.gpu_glyph_returned is true
   - Expected: evidence.gpu_glyph_readback_matched is true
   - Expected: evidence.production_ready is true
   - Expected: evidence.status_code equals `vector-font-glyph-readback-matched`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- accel
- accel
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

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- accel
   - Expected: evidence.execution.device_executed is true
   - Expected: evidence.gpu_glyph_returned is false
   - Expected: evidence.gpu_glyph_readback_matched is false
   - Expected: evidence.production_ready is false
   - Expected: evidence.status_code equals `vector-font-glyph-return-missing`
   - Expected: evidence.reason equals `vector-font-gpu-glyph-return-missing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
