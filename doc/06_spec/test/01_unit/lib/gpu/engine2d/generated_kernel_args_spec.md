# Generated Kernel Args Specification

> <details>

<!-- sdn-diagram:id=generated_kernel_args_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=generated_kernel_args_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

generated_kernel_args_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=generated_kernel_args_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Generated Kernel Args Specification

## Scenarios

### Engine2D generated glyph raster args

#### fails closed before allocating invalid glyph raster args

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing_plan = generated_glyph_raster_args_pack(0, 2000, 16, 8, 14)
val missing_dst = generated_glyph_raster_args_pack(1000, 0, 16, 8, 14)
val bad_dims = generated_glyph_raster_args_pack(1000, 2000, 0, 8, 14)
val bad_font = generated_glyph_raster_args_pack(1000, 2000, 16, 8, 0)

expect(missing_plan.ready).to_equal(false)
expect(missing_plan.args_ptr).to_equal(0)
expect(missing_plan.reason).to_equal("missing-glyph-plan")
expect(missing_dst.reason).to_equal("missing-dst")
expect(bad_dims.reason).to_equal("invalid-dimensions")
expect(bad_font.reason).to_equal("invalid-font-size")
```

</details>

#### packs glyph_plan dst dimensions and font_size for generated kernels

1. generated glyph raster args free


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = generated_glyph_raster_args_pack(1000, 2000, 16, 8, 14)
val read = generated_glyph_raster_args_from_ptr(args.args_ptr)

expect(args.ready).to_equal(true)
expect(args.args_ptr > 0).to_equal(true)
expect(args.reason).to_equal("ready")
expect(read.ready).to_equal(true)
expect(read.glyph_plan).to_equal(1000)
expect(read.dst).to_equal(2000)
expect(read.width).to_equal(16)
expect(read.height).to_equal(8)
expect(read.font_size).to_equal(14)
expect(read.summary()).to_contain("font_size=14")

generated_glyph_raster_args_free(args)
```

</details>

#### feeds generated glyph provenance with a real args pointer

1. generated glyph raster args free


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = generated_glyph_raster_args_pack(1000, 2000, 16, 8, 14)

val provenance = generated_2d_operation_provenance("opencl", GENERATED_2D_GLYPH, 16, 8, true, true, args.args_ptr)

expect(args.ready).to_equal(true)
expect(provenance.ready).to_equal(true)
expect(provenance.args_ready).to_equal(true)
expect(provenance.generated_operation).to_equal(GENERATED_2D_GLYPH)
expect(provenance.entry_name).to_equal("simple_2d_glyph_raster_u32")
expect(provenance.cpu_preprocess_required).to_equal(false)

generated_glyph_raster_args_free(args)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/generated_kernel_args_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine2D generated glyph raster args

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
