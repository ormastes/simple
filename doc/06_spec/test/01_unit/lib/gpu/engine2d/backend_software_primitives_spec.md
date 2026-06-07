# Backend Software Primitives Specification

> 1. var b = SoftwareBackend create

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
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Software Primitives Specification

## Scenarios

### SoftwareBackend primitive rendering

#### draw_rect_filled fills its interior

1. var b = SoftwareBackend create

2. b clear

3. b draw rect filled
   - Expected: p[4 * 32 + 4] equals `0xFFFF0000u32`

4. b shutdown


<details>
<summary>Executable SPipe</summary>

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

#### draw_circle_filled writes its center (regression)

1. var b = SoftwareBackend create

2. b clear

3. b draw circle filled
   - Expected: p[16 * 32 + 16] equals `0xFF00FF00u32`

4. b shutdown


<details>
<summary>Executable SPipe</summary>

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

1. var b = SoftwareBackend create

2. b clear

3. b draw line
   - Expected: p[16 * 32 + 15] equals `0xFF0000FFu32`

4. b shutdown


<details>
<summary>Executable SPipe</summary>

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

1. var b = SoftwareBackend create

2. b clear

3. b draw gradient rect
   - Expected: top != BG is true
   - Expected: bot != BG is true
   - Expected: top != bot is true

4. b shutdown


<details>
<summary>Executable SPipe</summary>

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

1. var b = SoftwareBackend create

2. b clear

3. b draw rounded rect
   - Expected: p[4 * 32 + 16] equals `0xFFFFFF00u32`
   - Expected: p[4 * 32 + 4] equals `BG`

4. b shutdown


<details>
<summary>Executable SPipe</summary>

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

1. var b = SoftwareBackend create

2. b clear

3. b draw text

4. b shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = SoftwareBackend.create()
if b.init(48, 16):
    b.clear(BG)
    b.draw_text(1, 2, "Hi", 0xFFFFFFFFu32, 8)
    val p = b.read_pixels()
    var n = 0
    var i = 0
    while i < p.len():
        if p[i] != BG:
            n = n + 1
        i = i + 1
    expect(n).to_be_greater_than(0)
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
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
