# Backend Software Primitives Specification

> <details>

<!-- sdn-diagram:id=backend_software_primitives_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_software_primitives_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_software_primitives_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_software_primitives_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Software Primitives Specification

## Scenarios

### SoftwareBackend primitive rendering

#### draw_rect_filled fills its interior

- var b = SoftwareBackend create
- b clear
- b draw rect filled
   - Expected: p[4 * 32 + 4] equals `0xFFFF0000u32`
- b shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = SoftwareBackend.create()
if b.init(32, 32):
    b.clear(BG)
    b.draw_rect_filled(2, 2, 10, 10, 0xFFFF0000u32)
    val p = b.read_pixels()
    expect(p[4 * 32 + 4]).to_equal(0xFFFF0000u32)
    b.shutdown()
```

</details>

#### draw_rect_filled respects active clip bounds

- var b = SoftwareBackend create
- b clear
- b set clip
- b draw rect filled
   - Expected: p[3 * 32 + 3] equals `0xFFFF0000u32`
   - Expected: p[5 * 32 + 5] equals `BG`
- b shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = SoftwareBackend.create()
if b.init(32, 32):
    b.clear(BG)
    b.set_clip(0, 0, 4, 4)
    b.draw_rect_filled(2, 2, 8, 8, 0xFFFF0000u32)
    val p = b.read_pixels()
    expect(p[3 * 32 + 3]).to_equal(0xFFFF0000u32)
    expect(p[5 * 32 + 5]).to_equal(BG)
    b.shutdown()
```

</details>

#### draw_circle_filled writes its center (regression)

- var b = SoftwareBackend create
- b clear
- b draw circle filled
   - Expected: p[16 * 32 + 16] equals `0xFF00FF00u32`
- b shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = SoftwareBackend.create()
if b.init(32, 32):
    b.clear(BG)
    b.draw_circle_filled(16, 16, 8, 0xFF00FF00u32)
    val p = b.read_pixels()
    expect(p[16 * 32 + 16]).to_equal(0xFF00FF00u32)
    b.shutdown()
```

</details>

#### draw_line writes pixels along the line (regression)

- var b = SoftwareBackend create
- b clear
- b draw line
   - Expected: p[16 * 32 + 15] equals `0xFF0000FFu32`
- b shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = SoftwareBackend.create()
if b.init(32, 32):
    b.clear(BG)
    b.draw_line(1, 16, 30, 16, 0xFF0000FFu32, 3)
    val p = b.read_pixels()
    expect(p[16 * 32 + 15]).to_equal(0xFF0000FFu32)
    b.shutdown()
```

</details>

#### draw_gradient_rect shades top-to-bottom (regression)

- var b = SoftwareBackend create
- b clear
- b draw gradient rect
   - Expected: top != BG is true
   - Expected: bot != BG is true
   - Expected: top != bot is true
- b shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = SoftwareBackend.create()
if b.init(32, 32):
    b.clear(BG)
    b.draw_gradient_rect(1, 1, 12, 28, 0xFFFF0000u32, 0xFF0000FFu32)
    val p = b.read_pixels()
    val top = p[2 * 32 + 6]
    val bot = p[26 * 32 + 6]
    expect(top != BG).to_equal(true)
    expect(bot != BG).to_equal(true)
    expect(top != bot).to_equal(true)
    b.shutdown()
```

</details>

#### draw_rounded_rect draws edge and rounds the corner (regression)

- var b = SoftwareBackend create
- b clear
- b draw rounded rect
   - Expected: p[4 * 32 + 16] equals `0xFFFFFF00u32`
   - Expected: p[4 * 32 + 4] equals `BG`
- b shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = SoftwareBackend.create()
if b.init(32, 32):
    b.clear(BG)
    b.draw_rounded_rect(4, 4, 24, 24, 5, 0xFFFFFF00u32)
    val p = b.read_pixels()
    expect(p[4 * 32 + 16]).to_equal(0xFFFFFF00u32)
    expect(p[4 * 32 + 4]).to_equal(BG)
    b.shutdown()
```

</details>

#### draw_text writes glyph pixels (regression)

- var b = SoftwareBackend create
- b clear
- b draw text
- b shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = SoftwareBackend.create()
if b.init(48, 16):
    b.clear(BG)
    b.draw_text(1, 2, "Hi", 0xFFFFFFFFu32, 8)
    val p = b.read_pixels()
    var n = 0
    var i = 0
    val pixel_count = p.len()
    while i < pixel_count:
        if p[i] != BG:
            n = n + 1
        i = i + 1
    expect(n).to_be_greater_than(0)
    b.shutdown()
```

</details>

#### draw_text clips offscreen spans on the fast path

- var full = SoftwareBackend create
- var left = SoftwareBackend create
- var right = SoftwareBackend create
- full clear
- left clear
- right clear
- full draw text
- left draw text
- right draw text
- full shutdown
- left shutdown
- right shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var full = SoftwareBackend.create()
var left = SoftwareBackend.create()
var right = SoftwareBackend.create()
if full.init(48, 16) and left.init(48, 16) and right.init(48, 16):
    full.clear(BG)
    left.clear(BG)
    right.clear(BG)
    full.draw_text(8, 2, "Hi", 0xFFFFFFFFu32, 8)
    left.draw_text(-4, 2, "Hi", 0xFFFFFFFFu32, 8)
    right.draw_text(44, 2, "Hi", 0xFFFFFFFFu32, 8)
    val full_p = full.read_pixels()
    val left_p = left.read_pixels()
    val right_p = right.read_pixels()
    var full_count = 0
    var left_count = 0
    var right_count = 0
    var i = 0
    val pixel_count = full_p.len()
    while i < pixel_count:
        if full_p[i] != BG:
            full_count = full_count + 1
        if left_p[i] != BG:
            left_count = left_count + 1
        if right_p[i] != BG:
            right_count = right_count + 1
        i = i + 1
    expect(left_count).to_be_greater_than(0)
    expect(right_count).to_be_greater_than(0)
    expect(left_count).to_be_less_than(full_count)
    expect(right_count).to_be_less_than(full_count)
    full.shutdown()
    left.shutdown()
    right.shutdown()
```

</details>

#### draw_text respects active clip bounds

- var b = SoftwareBackend create
- b clear
- b set clip
- b draw text
   - Expected: n equals `0`
- b shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = SoftwareBackend.create()
if b.init(48, 16):
    b.clear(BG)
    b.set_clip(32, 0, 8, 16)
    b.draw_text(1, 2, "Hi", 0xFFFFFFFFu32, 8)
    val p = b.read_pixels()
    var n = 0
    var i = 0
    val pixel_count = p.len()
    while i < pixel_count:
        if p[i] != BG:
            n = n + 1
        i = i + 1
    expect(n).to_equal(0)
    b.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/backend_software_primitives_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SoftwareBackend primitive rendering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
