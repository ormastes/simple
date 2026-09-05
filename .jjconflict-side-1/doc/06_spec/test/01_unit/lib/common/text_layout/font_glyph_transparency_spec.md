# Font Glyph Transparency Specification

> <details>

<!-- sdn-diagram:id=font_glyph_transparency_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=font_glyph_transparency_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

font_glyph_transparency_spec -> std
font_glyph_transparency_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=font_glyph_transparency_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Font Glyph Transparency Specification

## Scenarios

### font glyph transparency / alpha compositing

#### full coverage replaces the background with the foreground

- var buf: [u32] = [ argb
   - Expected: _r(out[0]) equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf: [u32] = [_argb(255, 0, 0, 0)]
val out = blit_glyph(buf, 1, 1, 0, 0, _glyph_1x1(255), _argb(255, 255, 255, 255))
expect(_r(out[0])).to_equal(255)
```

</details>

#### half coverage blends toward the foreground (midpoint)

- var buf: [u32] = [ argb
   - Expected: _r(out[0]) equals `128`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf: [u32] = [_argb(255, 0, 0, 0)]
val out = blit_glyph(buf, 1, 1, 0, 0, _glyph_1x1(128), _argb(255, 255, 255, 255))
# (255*128 + 0*127)/255 == 128
expect(_r(out[0])).to_equal(128)
```

</details>

#### zero coverage leaves the background unchanged

- var buf: [u32] = [ argb
   - Expected: _r(out[0]) equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf: [u32] = [_argb(255, 10, 20, 30)]
val out = blit_glyph(buf, 1, 1, 0, 0, _glyph_1x1(0), _argb(255, 255, 255, 255))
expect(_r(out[0])).to_equal(10)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/text_layout/font_glyph_transparency_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- font glyph transparency / alpha compositing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
