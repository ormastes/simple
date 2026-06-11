# Skia ASCII Fallback Glyph Specification

> Tests for ascii_fallback_glyph, ascii_glyph_to_bitmap_pixels, and ascii_glyph_advance_x — the minimal 5x7 ASCII debug font used when no real font is loaded.

<!-- sdn-diagram:id=ascii_fallback_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ascii_fallback_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ascii_fallback_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ascii_fallback_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia ASCII Fallback Glyph Specification

Tests for ascii_fallback_glyph, ascii_glyph_to_bitmap_pixels, and ascii_glyph_advance_x — the minimal 5x7 ASCII debug font used when no real font is loaded.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-ASCII-FALLBACK |
| Category | Stdlib |
| Difficulty | 1/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/skia/ascii_fallback_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for ascii_fallback_glyph, ascii_glyph_to_bitmap_pixels, and
ascii_glyph_advance_x — the minimal 5x7 ASCII debug font used when no real
font is loaded.

## Scenarios

### ascii_fallback

#### ascii_fallback_glyph(' '): returns 7 zeros

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = ascii_fallback_glyph(32)
expect(g.length()).to_equal(7)
expect(g[0]).to_equal(0)
expect(g[1]).to_equal(0)
expect(g[2]).to_equal(0)
expect(g[3]).to_equal(0)
expect(g[4]).to_equal(0)
expect(g[5]).to_equal(0)
expect(g[6]).to_equal(0)
```

</details>

#### ascii_fallback_glyph('0'): has top/bottom rows with 5 bits set

<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = ascii_fallback_glyph(48)
expect(g.length()).to_equal(7)
# Top row should have 5 contiguous pixels in the character (bits span 5 cols)
val top = g[0]
val bot = g[6]
# Count set bits in top row
var top_bits: i64 = 0
var i: i64 = 0
while i < 5:
    val m = 1 << i
    val set = (top & m) != 0
    if set:
        top_bits = top_bits + 1
    i = i + 1
# Count set bits in bottom row
var bot_bits: i64 = 0
var j: i64 = 0
while j < 5:
    val m = 1 << j
    val set = (bot & m) != 0
    if set:
        bot_bits = bot_bits + 1
    j = j + 1
expect(top_bits).to_be_greater_than(2)
expect(bot_bits).to_be_greater_than(2)
```

</details>

#### ascii_fallback_glyph('1'): has middle column (bit 2) set in several rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = ascii_fallback_glyph(49)
expect(g.length()).to_equal(7)
val mask = 0x04
var count: i64 = 0
var k: i64 = 0
while k < 7:
    val row = g[k]
    val is_on = (row & mask) != 0
    if is_on:
        count = count + 1
    k = k + 1
expect(count).to_be_greater_than(3)
```

</details>

#### ascii_fallback_glyph(9999): returns 7 zeros (out of range)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = ascii_fallback_glyph(9999)
expect(g.length()).to_equal(7)
var sum: i64 = 0
var i: i64 = 0
while i < 7:
    sum = sum + g[i]
    i = i + 1
expect(sum).to_equal(0)
```

</details>

#### ascii_glyph_to_bitmap_pixels: returns 35-element list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = ascii_glyph_to_bitmap_pixels(65)
expect(pixels.length()).to_equal(35)
```

</details>

#### ascii_glyph_advance_x(' ') == 0; ascii_glyph_advance_x('A') == 6

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adv_space = ascii_glyph_advance_x(32)
val adv_a = ascii_glyph_advance_x(65)
expect(adv_space).to_equal(0)
expect(adv_a).to_equal(6)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
