# Bitmap Font Offload Specification

> <details>

<!-- sdn-diagram:id=bitmap_font_offload_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bitmap_font_offload_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bitmap_font_offload_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bitmap_font_offload_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bitmap Font Offload Specification

## Scenarios

### Engine2D bitmap font offload evidence

#### marks CUDA bitmap font as GPU copy with CPU glyph preprocessing

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = bitmap_font_offload_evidence("cuda", 64, 32, true, true, 4096)

expect(evidence.generated_ready).to_equal(true)
expect(evidence.cpu_glyph_preprocess_required).to_equal(true)
expect(evidence.gpu_copy_upload_ready).to_equal(true)
expect(evidence.gpu_glyph_rasterized).to_equal(false)
expect(evidence.production_ready).to_equal(false)
expect(evidence.status_code).to_equal("gpu-copy-with-cpu-glyph")
expect(evidence.reason).to_equal("bitmap-font-glyphs-rasterized-on-cpu-then-uploaded")
expect(evidence.generated.generated_operation).to_equal("copy")
expect(evidence.diagnostic_text()).to_contain("family=bitmap_font")
```

</details>

#### keeps CPU SIMD bitmap font evidence as a CPU preprocess baseline

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = bitmap_font_offload_evidence("cpu_simd_x86", 64, 32, false, false, 0)

expect(evidence.generated_ready).to_equal(true)
expect(evidence.cpu_glyph_preprocess_required).to_equal(true)
expect(evidence.gpu_copy_upload_ready).to_equal(false)
expect(evidence.gpu_glyph_rasterized).to_equal(false)
expect(evidence.status_code).to_equal("cpu-glyph-baseline")
expect(evidence.reason).to_equal("bitmap-font-glyphs-rasterized-on-cpu")
expect(evidence.generated.compute_target).to_equal("cpu_simd")
expect(evidence.generated.entry_name).to_equal("RenderBackend.draw_text_or_text_blit")
```

</details>

#### fails closed when bitmap font generated copy is unavailable

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = bitmap_font_offload_evidence("opencl", 64, 32, false, false, 4096)

expect(evidence.generated_ready).to_equal(false)
expect(evidence.gpu_copy_upload_ready).to_equal(false)
expect(evidence.gpu_glyph_rasterized).to_equal(false)
expect(evidence.production_ready).to_equal(false)
expect(evidence.status_code).to_equal("opencl-runtime-or-queue-unavailable")
expect(evidence.reason).to_equal("runtime-not-ready")
```

</details>

#### uses the Engine2D font offload order before producing bitmap evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = bitmap_font_preferred_offload_evidence(["vulkan", "amd-hip", "cpu"], 64, 32, true, true, 4096)
val fallback = bitmap_font_preferred_offload_evidence(["unknown"], 64, 32, true, true, 4096)

expect(evidence.backend_name).to_equal("rocm")
expect(evidence.generated.backend_name).to_equal("rocm")
expect(evidence.generated_ready).to_equal(true)
expect(evidence.gpu_glyph_raster_plan_ready).to_equal(true)
expect(fallback.backend_name).to_equal("cpu")
expect(fallback.status_code).to_equal("cpu-glyph-baseline")
```

</details>

#### derives bitmap glyph raster readback checksum from the glyph mask

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expected_pixels = bitmap_glyph_raster_expected_pixels([1u32, 0u32, 3u32, 0u32], 2, 2, 0xff224466u32)
val expected_checksum = bitmap_glyph_raster_checksum(expected_pixels)
val direct_checksum = bitmap_glyph_raster_mask_checksum([1u32, 0u32, 3u32, 0u32], 2, 2, 0xff224466u32)
val evidence = bitmap_glyph_raster_mask_readback_evidence("cuda", [1u32, 0u32, 3u32, 0u32], 2, 2, 0xff224466u32, 4096, 7, 11, true, true, true, expected_checksum)

expect(expected_pixels).to_equal([0xff224466u32, 0u32, 0xff224466u32, 0u32])
expect(expected_checksum).to_be_greater_than(0)
expect(direct_checksum).to_equal(expected_checksum)
expect(evidence.execution.expected_checksum).to_equal(expected_checksum)
expect(evidence.execution.actual_checksum).to_equal(expected_checksum)
expect(evidence.gpu_glyph_rasterized).to_equal(true)
expect(evidence.production_ready).to_equal(true)
expect(evidence.status_code).to_equal("gpu-glyph-raster-readback-matched")
```

</details>

#### uses the Engine2D font offload order before bitmap glyph readback proof

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expected_checksum = bitmap_glyph_raster_mask_checksum([1u32, 0u32, 3u32, 0u32], 2, 2, 0xff224466u32)
val evidence = bitmap_glyph_raster_preferred_mask_readback_evidence(["vulkan", "amd-hip", "cpu"], [1u32, 0u32, 3u32, 0u32], 2, 2, 0xff224466u32, 4096, 7, 11, true, true, true, expected_checksum)
val fallback = bitmap_glyph_raster_preferred_mask_readback_evidence(["unknown"], [1u32, 0u32, 3u32, 0u32], 2, 2, 0xff224466u32, 4096, 7, 11, true, true, true, expected_checksum)

expect(evidence.backend_name).to_equal("rocm")
expect(evidence.submit.request.plan.compute_target).to_equal("hip")
expect(evidence.execution.device_executed).to_equal(true)
expect(evidence.production_ready).to_equal(true)
expect(evidence.status_code).to_equal("gpu-glyph-raster-readback-matched")
expect(fallback.backend_name).to_equal("cpu")
expect(fallback.execution.device_executed).to_equal(false)
expect(fallback.production_ready).to_equal(false)
expect(fallback.status_code).to_equal("gpu-glyph-raster-not-submitted")
```

</details>

#### keeps mask-derived bitmap glyph raster evidence incomplete on invalid masks

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = bitmap_glyph_raster_mask_readback_evidence("cuda", [1u32], 2, 2, 0xff224466u32, 4096, 7, 11, true, true, true, 999)

expect(bitmap_glyph_raster_mask_checksum([1u32], 2, 2, 0xff224466u32)).to_equal(0)
expect(evidence.execution.expected_checksum).to_equal(0)
expect(evidence.gpu_glyph_rasterized).to_equal(false)
expect(evidence.production_ready).to_equal(false)
expect(evidence.status_code).to_equal("gpu-glyph-raster-invalid-expected-checksum")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/bitmap_font_offload_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine2D bitmap font offload evidence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
