# Golden Gate Specification

## Scenarios

### wm_compare golden-image gate

#### solid_fill golden

#### loads from disk

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = check_golden(scene_solid_fill())
expect(r.loaded_ok).to_equal(true)
```

</details>

#### matches the golden exactly

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = check_golden(scene_solid_fill())
expect(r.pass_gate).to_equal(true)
```

</details>

#### fill_rect_row_edge golden

#### loads from disk

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = check_golden(scene_fill_rect_row_edge())
expect(r.loaded_ok).to_equal(true)
```

</details>

#### stays within drift budget

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = check_golden(scene_fill_rect_row_edge())
expect(r.pass_gate).to_equal(true)
```

</details>

#### text_with_bg golden

#### loads from disk

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = check_golden(scene_text_with_bg())
expect(r.loaded_ok).to_equal(true)
```

</details>

#### stays within drift budget

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = check_golden(scene_text_with_bg())
expect(r.pass_gate).to_equal(true)
```

</details>

#### glass_blend golden

#### loads from disk

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = check_golden(scene_glass_blend())
expect(r.loaded_ok).to_equal(true)
```

</details>

#### stays within drift budget

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = check_golden(scene_glass_blend())
expect(r.pass_gate).to_equal(true)
```

</details>

#### PPM encoder/decoder roundtrip

#### round-trips a freshly rendered scene exactly

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = render_framebuffer_baseline(scene_solid_fill())
val bytes = encode_ppm_p6(32u32, 16u32, pixels)
val decoded = decode_ppm_p6(bytes)
expect(decoded.len() == pixels.len()).to_equal(true)
```

</details>

#### writes a P6 magic header

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = render_framebuffer_baseline(scene_solid_fill())
val bytes = encode_ppm_p6(32u32, 16u32, pixels)
# 'P' = 80, '6' = 54, '\n' = 10
expect(bytes[0] == 80u8).to_equal(true)
expect(bytes[1] == 54u8).to_equal(true)
expect(bytes[2] == 10u8).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/system/wm_compare/golden_gate_spec.spl` |
| Updated | 2026-05-31 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- wm_compare golden-image gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

