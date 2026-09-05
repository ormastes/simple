# Blink Visual-Effect Lowering Specification

> Parsing a `box-shadow` is only half the job; the other half is turning it into something the rasterizer can actually draw. blink's paint output is a flat list of axis-aligned rects, each with one solid colour — that is the entire drawing vocabulary, and these examples pin exactly what it can and cannot express.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blink Visual-Effect Lowering Specification

Parsing a `box-shadow` is only half the job; the other half is turning it into something the rasterizer can actually draw. blink's paint output is a flat list of axis-aligned rects, each with one solid colour — that is the entire drawing vocabulary, and these examples pin exactly what it can and cannot express.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink |
| Status | Active |
| Source | `test/01_unit/lib/blink/paint/effect_paint_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Parsing a `box-shadow` is only half the job; the other half is turning it into
something the rasterizer can actually draw. blink's paint output is a flat list
of axis-aligned rects, each with one solid colour — that is the entire drawing
vocabulary, and these examples pin exactly what it can and cannot express.

Shadows become an offset, spread rect plus concentric alpha bands standing in
for blur. Gradients become solid strips. Transforms move and scale the rect.

Where the vocabulary runs out, I want an error, not an approximation dressed up
as success: an `inset` shadow is a clipped inner ring, a rotated box is a
quadrilateral, and a diagonal gradient's colour bands do not follow any rect
edge. All three are refused rather than painted wrong.

@manual_section Browser Rendering

## Scenarios

### paint_box_shadow

#### offsets the shadow rect by the shadow's offset and leaves size alone

- offsets the shadow rect by the shadow's offset and leaves size alone
- a 100x50 box at (10, 20) with a 5px/7px unblurred shadow
- one rect is emitted — no blur means no bands
   - Expected: r.is_ok() is true
   - Expected: rects.rect_count equals `1`
- the rect sits at box origin plus offset: 10+5 = 15, 20+7 = 27
   - Expected: rects.rect_x[0] equals `15`
   - Expected: rects.rect_y[0] equals `27`
- with no spread the shadow is exactly the box's size
   - Expected: rects.rect_w[0] equals `100`
   - Expected: rects.rect_h[0] equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("offsets the shadow rect by the shadow's offset and leaves size alone")
step("a 100x50 box at (10, 20) with a 5px/7px unblurred shadow")
var rects = PaintChunkRects.create()
val r = paint_box_shadow(rects, 10.0, 20.0, 100.0, 50.0, _shadow("5px 7px black"))

step("one rect is emitted — no blur means no bands")
expect(r.is_ok()).to_equal(true)
expect(rects.rect_count).to_equal(1)

step("the rect sits at box origin plus offset: 10+5 = 15, 20+7 = 27")
expect(rects.rect_x[0]).to_equal(15)
expect(rects.rect_y[0]).to_equal(27)

step("with no spread the shadow is exactly the box's size")
expect(rects.rect_w[0]).to_equal(100)
expect(rects.rect_h[0]).to_equal(50)
```

</details>

#### grows the shadow by the spread on every side

- grows the shadow by the spread on every side
- the same box with a 10px spread and no offset
- spread outsets each edge by 10, so origin moves back by 10
   - Expected: rects.rect_x[0] equals `0`
   - Expected: rects.rect_y[0] equals `10`
- and each dimension grows by 10 on BOTH sides: 100+20 = 120, 50+20 = 70
   - Expected: rects.rect_w[0] equals `120`
   - Expected: rects.rect_h[0] equals `70`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("grows the shadow by the spread on every side")
step("the same box with a 10px spread and no offset")
var rects = PaintChunkRects.create()
paint_box_shadow(rects, 10.0, 20.0, 100.0, 50.0, _shadow("0 0 0 10px black"))

step("spread outsets each edge by 10, so origin moves back by 10")
expect(rects.rect_x[0]).to_equal(0)
expect(rects.rect_y[0]).to_equal(10)

step("and each dimension grows by 10 on BOTH sides: 100+20 = 120, 50+20 = 70")
expect(rects.rect_w[0]).to_equal(120)
expect(rects.rect_h[0]).to_equal(70)
```

</details>

#### approximates blur with four outset bands of rising alpha plus the core

- approximates blur with four outset bands of rising alpha plus the core
- an 8px blurred shadow on a 100x50 box at the origin
- four blur bands plus the solid core rect = 5 rects
   - Expected: n equals `5`
   - Expected: m equals ``
   - Expected: rects.rect_count equals `5`
- band 0 is the outermost: outset 8*(4-0)/4 = 8, so it starts at -8
   - Expected: rects.rect_x[0] equals `-8`
   - Expected: rects.rect_w[0] equals `116`
- band 0 is also the faintest: alpha 255 * (0+1)/4 = 63.75 -> 64
   - Expected: rects.colour[0] equals `64 * 16777216`
- band 3 is the innermost: outset 8*(4-3)/4 = 2, alpha 255*4/4 = 255
   - Expected: rects.rect_x[3] equals `-2`
   - Expected: rects.rect_w[3] equals `104`
- the core is painted last, unoutset and fully opaque, so it wins the overlap
   - Expected: rects.rect_x[4] equals `0`
   - Expected: rects.rect_w[4] equals `100`
   - Expected: rects.rect_h[4] equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("approximates blur with four outset bands of rising alpha plus the core")
step("an 8px blurred shadow on a 100x50 box at the origin")
var rects = PaintChunkRects.create()
val r = paint_box_shadow(rects, 0.0, 0.0, 100.0, 50.0, _shadow("0 0 8px black"))

step("four blur bands plus the solid core rect = 5 rects")
match r:
    Ok(n):
        expect(n).to_equal(5)
    Err(m):
        expect(m).to_equal("")
expect(rects.rect_count).to_equal(5)

step("band 0 is the outermost: outset 8*(4-0)/4 = 8, so it starts at -8")
expect(rects.rect_x[0]).to_equal(-8)
# 100 + 2*8
expect(rects.rect_w[0]).to_equal(116)

step("band 0 is also the faintest: alpha 255 * (0+1)/4 = 63.75 -> 64")
# Packed 0xAARRGGBB over an opaque-black shadow: only the alpha byte varies.
expect(rects.colour[0]).to_equal(64 * 16777216)

step("band 3 is the innermost: outset 8*(4-3)/4 = 2, alpha 255*4/4 = 255")
expect(rects.rect_x[3]).to_equal(-2)
expect(rects.rect_w[3]).to_equal(104)

step("the core is painted last, unoutset and fully opaque, so it wins the overlap")
expect(rects.rect_x[4]).to_equal(0)
expect(rects.rect_w[4]).to_equal(100)
expect(rects.rect_h[4]).to_equal(50)
```

</details>

#### paints nothing for a spread that collapses the box

- paints nothing for a spread that collapses the box
- a 20x20 box with a -15px spread, which removes 30 from each dimension
- a collapsed shadow is a real CSS outcome — zero rects, not an error
   - Expected: n equals `0`
   - Expected: m equals ``
   - Expected: rects.rect_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("paints nothing for a spread that collapses the box")
step("a 20x20 box with a -15px spread, which removes 30 from each dimension")
var rects = PaintChunkRects.create()
val r = paint_box_shadow(rects, 0.0, 0.0, 20.0, 20.0, _shadow("0 0 0 -15px black"))

step("a collapsed shadow is a real CSS outcome — zero rects, not an error")
match r:
    Ok(n):
        expect(n).to_equal(0)
    Err(m):
        expect(m).to_equal("")
expect(rects.rect_count).to_equal(0)
```

</details>

#### refuses an inset shadow rather than painting it outside the box

- refuses an inset shadow rather than painting it outside the box
- lower an inset shadow
- an inner ring clipped to the padding box has no flat-rect form, so it errors
   - Expected: r.is_ok() is false
- and nothing was appended on the way to failing
   - Expected: rects.rect_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("refuses an inset shadow rather than painting it outside the box")
step("lower an inset shadow")
var rects = PaintChunkRects.create()
val r = paint_box_shadow(rects, 0.0, 0.0, 100.0, 50.0, _shadow("inset 2px 2px black"))

step("an inner ring clipped to the padding box has no flat-rect form, so it errors")
expect(r.is_ok()).to_equal(false)

step("and nothing was appended on the way to failing")
expect(rects.rect_count).to_equal(0)
```

</details>

### paint_box_shadows

#### paints layers back-to-front so the first-authored layer ends up on top

- paints layers back-to-front so the first-authored layer ends up on top
- a two-layer shadow whose layers have distinct offsets
   - Expected: m equals ``
- two rects, and the LAST-authored layer (offset 5) is appended first
   - Expected: rects.rect_count equals `2`
   - Expected: rects.rect_x[0] equals `5`
- so the first-authored layer (offset 1) is appended last and overwrites it
   - Expected: rects.rect_x[1] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("paints layers back-to-front so the first-authored layer ends up on top")
step("a two-layer shadow whose layers have distinct offsets")
var rects = PaintChunkRects.create()
var layers: [BoxShadow] = []
match parse_box_shadow("1px 1px red, 5px 5px blue"):
    Ok(ls):
        layers = ls
    Err(m):
        expect(m).to_equal("")
paint_box_shadows(rects, 0.0, 0.0, 10.0, 10.0, layers)

step("two rects, and the LAST-authored layer (offset 5) is appended first")
expect(rects.rect_count).to_equal(2)
expect(rects.rect_x[0]).to_equal(5)

step("so the first-authored layer (offset 1) is appended last and overwrites it")
expect(rects.rect_x[1]).to_equal(1)
```

</details>

### transform_bounds

#### returns the moved rect for a pure translation

- returns the moved rect for a pure translation
- translate a 100x50 box at the origin by (10, 20)
   - Expected: e equals ``
- every corner shifts by the same vector, so the bounds are the box moved
   - Expected: b.0 equals `10.0`
   - Expected: b.1 equals `20.0`
   - Expected: b.2 equals `110.0`
   - Expected: b.3 equals `70.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns the moved rect for a pure translation")
step("translate a 100x50 box at the origin by (10, 20)")
var t = Transform2D.identity()
match parse_transform("translate(10px, 20px)"):
    Ok(m):
        t = m
    Err(e):
        expect(e).to_equal("")
val b = transform_bounds(t, 0.0, 0.0, 100.0, 50.0)

step("every corner shifts by the same vector, so the bounds are the box moved")
expect(b.0).to_equal(10.0)
expect(b.1).to_equal(20.0)
expect(b.2).to_equal(110.0)
expect(b.3).to_equal(70.0)
```

</details>

#### grows the bounds of a rotated box beyond the box itself

- grows the bounds of a rotated box beyond the box itself
- rotate a 100x50 box by 45 degrees
   - Expected: e equals ``
- the diagonal projects onto both axes, so the bounds width is (100+50)/sqrt(2) ~= 106.07
   - Expected: w > 106.0 and w < 106.1 is true
- which is strictly larger than the 100 the box occupied — the bounds are NOT the shape
   - Expected: w > 100.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("grows the bounds of a rotated box beyond the box itself")
step("rotate a 100x50 box by 45 degrees")
var t = Transform2D.identity()
match parse_transform("rotate(45deg)"):
    Ok(m):
        t = m
    Err(e):
        expect(e).to_equal("")
val b = transform_bounds(t, 0.0, 0.0, 100.0, 50.0)

step("the diagonal projects onto both axes, so the bounds width is (100+50)/sqrt(2) ~= 106.07")
val w = b.2 - b.0
expect(w > 106.0 and w < 106.1).to_equal(true)

step("which is strictly larger than the 100 the box occupied — the bounds are NOT the shape")
expect(w > 100.0).to_equal(true)
```

</details>

### paint_transformed_rect

#### scales a box about the origin

- scales a box about the origin
- scale a 10x10 box at (4, 6) by 2
   - Expected: e equals ``
- scaling about the origin doubles the position too: 4*2 = 8, 6*2 = 12
   - Expected: rects.rect_x[0] equals `8`
   - Expected: rects.rect_y[0] equals `12`
- and doubles the size: 10*2 = 20
   - Expected: rects.rect_w[0] equals `20`
   - Expected: rects.rect_h[0] equals `20`
- the fill colour is packed 0xAARRGGBB, so opaque red is 0xFFFF0000
   - Expected: rects.colour[0] equals `4294901760`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("scales a box about the origin")
step("scale a 10x10 box at (4, 6) by 2")
var rects = PaintChunkRects.create()
var t = Transform2D.identity()
match parse_transform("scale(2)"):
    Ok(m):
        t = m
    Err(e):
        expect(e).to_equal("")
paint_transformed_rect(rects, t, 4.0, 6.0, 10.0, 10.0, from_rgba(255, 0, 0, 255))

step("scaling about the origin doubles the position too: 4*2 = 8, 6*2 = 12")
expect(rects.rect_x[0]).to_equal(8)
expect(rects.rect_y[0]).to_equal(12)

step("and doubles the size: 10*2 = 20")
expect(rects.rect_w[0]).to_equal(20)
expect(rects.rect_h[0]).to_equal(20)

step("the fill colour is packed 0xAARRGGBB, so opaque red is 0xFFFF0000")
expect(rects.colour[0]).to_equal(4294901760)
```

</details>

#### refuses a rotated box rather than painting its bounding box

- refuses a rotated box rather than painting its bounding box
- paint a box under a 30-degree rotation
   - Expected: e equals ``
- the true shape is a quadrilateral; its bounds would colour pixels the element does not cover
   - Expected: r.is_ok() is false
   - Expected: rects.rect_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("refuses a rotated box rather than painting its bounding box")
step("paint a box under a 30-degree rotation")
var rects = PaintChunkRects.create()
var t = Transform2D.identity()
match parse_transform("rotate(30deg)"):
    Ok(m):
        t = m
    Err(e):
        expect(e).to_equal("")
val r = paint_transformed_rect(rects, t, 0.0, 0.0, 10.0, 10.0, from_rgba(0, 0, 0, 255))

step("the true shape is a quadrilateral; its bounds would colour pixels the element does not cover")
expect(r.is_ok()).to_equal(false)
expect(rects.rect_count).to_equal(0)
```

</details>

#### paints an exact quarter turn, whose shape really is its bounds

- paints an exact quarter turn, whose shape really is its bounds
- rotate a 40-wide, 10-tall box at the origin by exactly 90 degrees
   - Expected: e equals ``
- a quarter turn maps a rect onto a rect, so painting the bounds is exact, not an approximation
   - Expected: r.is_ok() is true
   - Expected: rects.rect_count equals `1`
- clockwise-in-y-down 90deg sends (x,y) to (-y,x): the corners (0,0) and (40,10) become (0,0) and (-10,40)
- so the bounds run x from -10 to 0 and y from 0 to 40 — origin (-10, 0)
   - Expected: rects.rect_x[0] equals `-10`
   - Expected: rects.rect_y[0] equals `0`
- width and height swap: the 40-wide, 10-tall box becomes 10 wide and 40 tall
   - Expected: rects.rect_w[0] equals `10`
   - Expected: rects.rect_h[0] equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("paints an exact quarter turn, whose shape really is its bounds")
step("rotate a 40-wide, 10-tall box at the origin by exactly 90 degrees")
var rects = PaintChunkRects.create()
var t = Transform2D.identity()
match parse_transform("rotate(90deg)"):
    Ok(m):
        t = m
    Err(e):
        expect(e).to_equal("")
val r = paint_transformed_rect(rects, t, 0.0, 0.0, 40.0, 10.0, from_rgba(0, 0, 255, 255))

step("a quarter turn maps a rect onto a rect, so painting the bounds is exact, not an approximation")
expect(r.is_ok()).to_equal(true)
expect(rects.rect_count).to_equal(1)

step("clockwise-in-y-down 90deg sends (x,y) to (-y,x): the corners (0,0) and (40,10) become (0,0) and (-10,40)")
step("so the bounds run x from -10 to 0 and y from 0 to 40 — origin (-10, 0)")
expect(rects.rect_x[0]).to_equal(-10)
expect(rects.rect_y[0]).to_equal(0)

step("width and height swap: the 40-wide, 10-tall box becomes 10 wide and 40 tall")
expect(rects.rect_w[0]).to_equal(10)
expect(rects.rect_h[0]).to_equal(40)
```

</details>

### gradient_color_at

#### interpolates linearly between the two bracketing stops

- interpolates linearly between the two bracketing stops
- a red-to-blue gradient sampled at its midpoint
- halfway from 255 to 0 is 127.5, rounded to 128
   - Expected: c.r equals `128`
- and halfway from 0 to 255 is likewise 128
   - Expected: c.b equals `128`
- alpha is 255 at both ends, so it stays 255
   - Expected: c.a equals `255`
   - Expected: m equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("interpolates linearly between the two bracketing stops")
step("a red-to-blue gradient sampled at its midpoint")
match parse_linear_gradient("linear-gradient(red, blue)"):
    Ok(g):
        val c = gradient_color_at(g, 0.5)

        step("halfway from 255 to 0 is 127.5, rounded to 128")
        expect(c.r).to_equal(128)

        step("and halfway from 0 to 255 is likewise 128")
        expect(c.b).to_equal(128)

        step("alpha is 255 at both ends, so it stays 255")
        expect(c.a).to_equal(255)
    Err(m):
        expect(m).to_equal("")
```

</details>

#### clamps to the end colours outside the stop range

- clamps to the end colours outside the stop range
- sample a red-to-blue gradient before its first stop
- CSS extends the first stop's colour backwards, so this is pure red
   - Expected: c.r equals `255`
   - Expected: c.b equals `0`
   - Expected: m equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clamps to the end colours outside the stop range")
step("sample a red-to-blue gradient before its first stop")
match parse_linear_gradient("linear-gradient(red, blue)"):
    Ok(g):
        val c = gradient_color_at(g, 0.0 - 1.0)

        step("CSS extends the first stop's colour backwards, so this is pure red")
        expect(c.r).to_equal(255)
        expect(c.b).to_equal(0)
    Err(m):
        expect(m).to_equal("")
```

</details>

### paint_linear_gradient

#### splits a to-bottom gradient into seamless horizontal strips

- splits a to-bottom gradient into seamless horizontal strips
- a black-to-white to-bottom gradient over a 100x100 box, in 4 bands
   - Expected: r.is_ok() is true
- four bands, each a full-width strip 100/4 = 25 tall
   - Expected: rects.rect_count equals `4`
   - Expected: rects.rect_w[0] equals `100`
   - Expected: rects.rect_h[0] equals `25`
- band edges abut with no seam: band 1 starts where band 0 ended
   - Expected: rects.rect_y[0] equals `0`
   - Expected: rects.rect_y[1] equals `25`
   - Expected: rects.rect_y[2] equals `50`
   - Expected: rects.rect_y[3] equals `75`
- band 0 samples its midpoint 0.5/4 = 0.125, giving grey 0.125*255 = 31.875 -> 32
   - Expected: rects.colour[0] equals `4280295456`
- band 3 samples 3.5/4 = 0.875, giving 223 — brighter, since to-bottom runs black to white
   - Expected: rects.colour[3] equals `4292861919`
   - Expected: m equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("splits a to-bottom gradient into seamless horizontal strips")
step("a black-to-white to-bottom gradient over a 100x100 box, in 4 bands")
var rects = PaintChunkRects.create()
match parse_linear_gradient("linear-gradient(black, white)"):
    Ok(g):
        val r = paint_linear_gradient(rects, 0.0, 0.0, 100.0, 100.0, g, 4)
        expect(r.is_ok()).to_equal(true)

        step("four bands, each a full-width strip 100/4 = 25 tall")
        expect(rects.rect_count).to_equal(4)
        expect(rects.rect_w[0]).to_equal(100)
        expect(rects.rect_h[0]).to_equal(25)

        step("band edges abut with no seam: band 1 starts where band 0 ended")
        expect(rects.rect_y[0]).to_equal(0)
        expect(rects.rect_y[1]).to_equal(25)
        expect(rects.rect_y[2]).to_equal(50)
        expect(rects.rect_y[3]).to_equal(75)

        step("band 0 samples its midpoint 0.5/4 = 0.125, giving grey 0.125*255 = 31.875 -> 32")
        # 0xFF202020 = 255<<24 | 32<<16 | 32<<8 | 32
        expect(rects.colour[0]).to_equal(4280295456)

        step("band 3 samples 3.5/4 = 0.875, giving 223 — brighter, since to-bottom runs black to white")
        # 0xFFDFDFDF
        expect(rects.colour[3]).to_equal(4292861919)
    Err(m):
        expect(m).to_equal("")
```

</details>

#### runs a to-top gradient against the pixel axis

- runs a to-top gradient against the pixel axis
- the same black-to-white gradient, but pointing to the top
- 0deg points up, so the FIRST (topmost) band is now the white end: 223
   - Expected: rects.colour[0] equals `4292861919`
- and the bottom band is the black end: 32
   - Expected: rects.colour[3] equals `4280295456`
   - Expected: m equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("runs a to-top gradient against the pixel axis")
step("the same black-to-white gradient, but pointing to the top")
var rects = PaintChunkRects.create()
match parse_linear_gradient("linear-gradient(to top, black, white)"):
    Ok(g):
        paint_linear_gradient(rects, 0.0, 0.0, 100.0, 100.0, g, 4)

        step("0deg points up, so the FIRST (topmost) band is now the white end: 223")
        expect(rects.colour[0]).to_equal(4292861919)

        step("and the bottom band is the black end: 32")
        expect(rects.colour[3]).to_equal(4280295456)
    Err(m):
        expect(m).to_equal("")
```

</details>

#### splits a to-right gradient into vertical strips

- splits a to-right gradient into vertical strips
- a to-right gradient over a 100x40 box in 2 bands
- bands now run along x: each is 100/2 = 50 wide and full height
   - Expected: rects.rect_w[0] equals `50`
   - Expected: rects.rect_h[0] equals `40`
   - Expected: rects.rect_x[0] equals `0`
   - Expected: rects.rect_x[1] equals `50`
   - Expected: m equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("splits a to-right gradient into vertical strips")
step("a to-right gradient over a 100x40 box in 2 bands")
var rects = PaintChunkRects.create()
match parse_linear_gradient("linear-gradient(to right, black, white)"):
    Ok(g):
        paint_linear_gradient(rects, 0.0, 0.0, 100.0, 40.0, g, 2)

        step("bands now run along x: each is 100/2 = 50 wide and full height")
        expect(rects.rect_w[0]).to_equal(50)
        expect(rects.rect_h[0]).to_equal(40)
        expect(rects.rect_x[0]).to_equal(0)
        expect(rects.rect_x[1]).to_equal(50)
    Err(m):
        expect(m).to_equal("")
```

</details>

#### refuses a diagonal gradient rather than snapping it to an axis

- refuses a diagonal gradient rather than snapping it to an axis
- lower a 45-degree gradient
- its iso-colour lines follow no rect edge, so no strip decomposition is faithful
   - Expected: r.is_ok() is false
   - Expected: rects.rect_count equals `0`
   - Expected: m equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("refuses a diagonal gradient rather than snapping it to an axis")
step("lower a 45-degree gradient")
var rects = PaintChunkRects.create()
match parse_linear_gradient("linear-gradient(45deg, black, white)"):
    Ok(g):
        val r = paint_linear_gradient(rects, 0.0, 0.0, 100.0, 100.0, g, 4)

        step("its iso-colour lines follow no rect edge, so no strip decomposition is faithful")
        expect(r.is_ok()).to_equal(false)
        expect(rects.rect_count).to_equal(0)
    Err(m):
        expect(m).to_equal("")
```

</details>

#### refuses a non-positive band count

- refuses a non-positive band count
- ask for zero bands
- zero bands would paint nothing while reporting success — an error instead
   - Expected: r.is_ok() is false
   - Expected: m equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("refuses a non-positive band count")
step("ask for zero bands")
var rects = PaintChunkRects.create()
match parse_linear_gradient("linear-gradient(black, white)"):
    Ok(g):
        val r = paint_linear_gradient(rects, 0.0, 0.0, 10.0, 10.0, g, 0)

        step("zero bands would paint nothing while reporting success — an error instead")
        expect(r.is_ok()).to_equal(false)
    Err(m):
        expect(m).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-BLINK-PAINT-EFFECTS-002`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `171c71028ae9de0ee6baa6de8f0ab456c5126ded837f948c0a3411d3902c5a33`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `171c71028ae9de0ee6baa6de8f0ab456c5126ded837f948c0a3411d3902c5a33`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `171c71028ae9de0ee6baa6de8f0ab456c5126ded837f948c0a3411d3902c5a33`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/blink/paint/effect_paint_spec.spl
mirror: doc/06_spec/01_unit/lib/blink/paint/effect_paint_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/lib/blink/paint/effect_paint_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/blink/paint/effect_paint_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/blink/paint/effect_paint_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 60 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/blink/paint/effect_paint_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/blink/paint/effect_paint_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'offsets the shadow rect by the shadow's offset and leaves size alone' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/blink/paint/effect_paint_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'grows the shadow by the spread on every side' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/blink/paint/effect_paint_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'approximates blur with four outset bands of rising alpha plus the core' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
