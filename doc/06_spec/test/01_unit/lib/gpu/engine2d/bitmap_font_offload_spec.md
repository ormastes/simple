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
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bitmap Font Offload Specification

## Scenarios

### Engine2D bitmap font offload evidence

#### marks CUDA bitmap font as GPU raster plan pending readback

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = bitmap_font_offload_evidence("cuda", 64, 32, true, true, 4096)

expect(evidence.generated_ready).to_equal(true)
expect(evidence.cpu_glyph_preprocess_required).to_equal(true)
expect(evidence.gpu_copy_upload_ready).to_equal(true)
expect(evidence.gpu_glyph_raster_plan_ready).to_equal(true)
expect(evidence.gpu_glyph_rasterized).to_equal(false)
expect(evidence.production_ready).to_equal(false)
expect(evidence.status_code).to_equal("gpu-raster-plan-without-readback")
expect(evidence.reason).to_equal("bitmap-font-gpu-raster-kernel-ready-readback-required")
expect(evidence.generated.generated_operation).to_equal("copy")
expect(evidence.glyph_raster_generated.generated_operation).to_equal("bitmap_glyph_raster")
expect(evidence.glyph_raster_generated.entry_name).to_equal("simple_2d_bitmap_glyph_raster_u32")
expect(evidence.glyph_raster_generated.cpu_preprocess_required).to_equal(false)
expect(evidence.diagnostic_text()).to_contain("family=bitmap_font")
expect(evidence.diagnostic_text()).to_contain("family=bitmap_glyph_raster")
```

</details>

#### keeps CPU SIMD bitmap font evidence as a CPU preprocess baseline

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = bitmap_font_offload_evidence("cpu_simd_x86", 64, 32, false, false, 0)

expect(evidence.generated_ready).to_equal(true)
expect(evidence.cpu_glyph_preprocess_required).to_equal(true)
expect(evidence.gpu_copy_upload_ready).to_equal(false)
expect(evidence.gpu_glyph_raster_plan_ready).to_equal(false)
expect(evidence.gpu_glyph_rasterized).to_equal(false)
expect(evidence.status_code).to_equal("cpu-glyph-baseline")
expect(evidence.reason).to_equal("bitmap-font-glyphs-rasterized-on-cpu")
expect(evidence.generated.compute_target).to_equal("cpu_simd")
expect(evidence.generated.entry_name).to_equal("RenderBackend.draw_text_or_text_blit")
expect(evidence.glyph_raster_generated.generated_operation).to_equal("bitmap_glyph_raster")
```

</details>

#### fails closed when bitmap font generated copy is unavailable

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = bitmap_font_offload_evidence("opencl", 64, 32, false, false, 4096)

expect(evidence.generated_ready).to_equal(false)
expect(evidence.gpu_copy_upload_ready).to_equal(false)
expect(evidence.gpu_glyph_raster_plan_ready).to_equal(false)
expect(evidence.gpu_glyph_rasterized).to_equal(false)
expect(evidence.production_ready).to_equal(false)
expect(evidence.status_code).to_equal("opencl-runtime-or-queue-unavailable")
expect(evidence.reason).to_equal("runtime-not-ready")
```

</details>

#### marks bitmap glyph raster production ready only after checksum-matched readback

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matched = bitmap_glyph_raster_readback_evidence("cuda", 8, 4, 4096, 0, 77, true, true, true, 1234, 1234)

expect(matched.gpu_glyph_rasterized).to_equal(true)
expect(matched.production_ready).to_equal(true)
expect(matched.execution.device_executed).to_equal(true)
expect(matched.status_code).to_equal("gpu-glyph-raster-readback-matched")
expect(matched.reason).to_equal("bitmap-glyph-raster-gpu-readback-matched")
expect(matched.diagnostic_text()).to_contain("op=bitmap_glyph_raster")
```

</details>

#### keeps bitmap glyph raster incomplete without readback or checksum match

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val no_readback = bitmap_glyph_raster_readback_evidence("cuda", 8, 4, 4096, 0, 77, true, true, false, 1234, 1234)
val mismatch = bitmap_glyph_raster_readback_evidence("cuda", 8, 4, 4096, 0, 77, true, true, true, 1234, 999)
val not_submitted = bitmap_glyph_raster_readback_evidence("cuda", 8, 4, 0, 0, 77, true, true, true, 1234, 1234)

expect(no_readback.gpu_glyph_rasterized).to_equal(false)
expect(no_readback.production_ready).to_equal(false)
expect(no_readback.status_code).to_equal("gpu-glyph-raster-readback-unavailable")
expect(mismatch.gpu_glyph_rasterized).to_equal(false)
expect(mismatch.status_code).to_equal("gpu-glyph-raster-readback-mismatch")
expect(not_submitted.gpu_glyph_rasterized).to_equal(false)
expect(not_submitted.status_code).to_equal("gpu-glyph-raster-not-submitted")
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
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
