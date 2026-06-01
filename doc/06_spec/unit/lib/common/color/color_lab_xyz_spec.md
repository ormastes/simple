# CIE XYZ / CIELAB Color Pipeline Specification

These checks cover numeric color conversion and the 8K packed-surface planning

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/color/color_lab_xyz_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

These checks cover numeric color conversion and the 8K packed-surface planning
contract used by GUI hardening. Tolerances here are only for floating-point
color conversion, not bitmap acceptance.

## Scenarios

### CIE XYZ and CIELAB

#### maps D65 white to neutral Lab

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val white = cie_xyz_d65_white()
val lab = cie_xyz_to_lab(white, white)
expect(color_nearly_equal(lab.l, 100.0, 0.0001)).to_equal(true)
expect(color_nearly_equal(lab.a, 0.0, 0.0001)).to_equal(true)
expect(color_nearly_equal(lab.b, 0.0, 0.0001)).to_equal(true)
expect(lab.white_point).to_equal("D65")
```

</details>

#### converts sRGB red through XYZ into published Lab vicinity

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val xyz = srgb_to_cie_xyz_d65(255, 0, 0)
expect(color_nearly_equal(xyz.x, 41.24564, 0.001)).to_equal(true)
expect(color_nearly_equal(xyz.y, 21.26729, 0.001)).to_equal(true)
expect(color_nearly_equal(xyz.z, 1.93339, 0.001)).to_equal(true)

val lab = srgb_to_lab_d65(255, 0, 0)
expect(color_nearly_equal(lab.l, 53.2408, 0.01)).to_equal(true)
expect(color_nearly_equal(lab.a, 80.0925, 0.01)).to_equal(true)
expect(color_nearly_equal(lab.b, 67.2032, 0.01)).to_equal(true)
```

</details>

#### round-trips Lab red back to packed ARGB red

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val white = cie_xyz_d65_white()
val lab = packed_argb_to_lab_d65(0xffff0000)
val xyz = lab_to_cie_xyz(lab, white)
val argb = cie_xyz_d65_to_srgb_packed_argb(xyz, 255)
val r = (argb / 65536) & 255
val g = (argb / 256) & 255
val b = argb & 255
val a = (argb / 16777216) & 255
expect(a).to_equal(255)
expect(r).to_be_greater_than(253)
expect(g).to_be_less_than(2)
expect(b).to_be_less_than(2)
```

</details>

### 8K packed color surface planning

#### keeps the default 8K hot path packed and lazy

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = plan_8k_uhd_surface()
expect(plan.width).to_equal(7680)
expect(plan.height).to_equal(4320)
expect(plan.bytes_per_pixel).to_equal(4)
expect(plan.framebuffer_bytes).to_equal(132710400)
expect(plan.lab_xyz_full_frame_bytes).to_equal(796262400)
expect(plan.uses_packed_hot_path).to_equal(true)
expect(plan.initializes_color_transforms).to_equal(false)
expect(plan.initializes_tiff_decoder).to_equal(false)
expect(plan.initializes_jpegxl_decoder).to_equal(false)
expect(plan.default_semantic_space).to_equal("cielab")
expect(plan.connection_space).to_equal("cie_xyz")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

