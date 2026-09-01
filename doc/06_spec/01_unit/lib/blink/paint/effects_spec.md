# Blink Visual-Effect Value Parsing Specification

> I want blink to understand the three visual-effect properties it was missing — `box-shadow`, `transform` and `linear-gradient()` — and, just as importantly, to tell me clearly when it does not understand a value.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blink Visual-Effect Value Parsing Specification

I want blink to understand the three visual-effect properties it was missing — `box-shadow`, `transform` and `linear-gradient()` — and, just as importantly, to tell me clearly when it does not understand a value.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink |
| Status | Active |
| Source | `test/01_unit/lib/blink/paint/effects_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

I want blink to understand the three visual-effect properties it was missing —
`box-shadow`, `transform` and `linear-gradient()` — and, just as importantly, to
tell me clearly when it does not understand a value.

Blink's earlier habit was to answer opaque black for any colour it could not
parse: a wrong pixel rather than an error, invisible to every smoke test. These
examples pin the opposite contract. Every entry point returns a `Result`, so an
unsupported unit, a malformed function or a nonsense keyword comes back as a
failure I can see, never as a substituted default.

Colours inside these values are not parsed here at all — they go through the
one shared CSS colour parser in `common.color.css`, so there is no second
colour implementation to drift.

@manual_section Browser Rendering

## Scenarios

### parse_box_shadow

#### reads offset, blur, spread and colour from a full four-length layer

- reads offset, blur, spread and colour from a full four-length layer
- parse a shadow with all four lengths and an explicit colour
- every field lands on the value authored in that position
   - Expected: r.is_ok() is true
   - Expected: layers.len() equals `1`
   - Expected: s.offset_x equals `2.0`
   - Expected: s.offset_y equals `4.0`
   - Expected: s.blur equals `6.0`
   - Expected: s.spread equals `8.0`
   - Expected: s.color.r equals `255`
   - Expected: s.color.g equals `0`
   - Expected: s.color.b equals `0`
   - Expected: s.color.a equals `255`
   - Expected: s.inset is false
   - Expected: m equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads offset, blur, spread and colour from a full four-length layer")
step("parse a shadow with all four lengths and an explicit colour")
val r = parse_box_shadow("2px 4px 6px 8px red")

step("every field lands on the value authored in that position")
expect(r.is_ok()).to_equal(true)
match r:
    Ok(layers):
        # One comma-free value is exactly one shadow layer.
        expect(layers.len()).to_equal(1)
        val s = layers[0 as i32]
        expect(s.offset_x).to_equal(2.0)
        expect(s.offset_y).to_equal(4.0)
        # Third length is blur, fourth is spread — CSS order.
        expect(s.blur).to_equal(6.0)
        expect(s.spread).to_equal(8.0)
        # `red` is CSS #FF0000, fully opaque.
        expect(s.color.r).to_equal(255)
        expect(s.color.g).to_equal(0)
        expect(s.color.b).to_equal(0)
        expect(s.color.a).to_equal(255)
        expect(s.inset).to_equal(false)
    Err(m):
        expect(m).to_equal("")
```

</details>

#### defaults blur and spread to zero when only the two offsets are given

- defaults blur and spread to zero when only the two offsets are given
- parse the minimal legal shadow: two offsets and a colour
- the two omitted lengths are the CSS initial 0, not garbage
   - Expected: layers[0 as i32].blur equals `0.0`
   - Expected: layers[0 as i32].spread equals `0.0`
   - Expected: m equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("defaults blur and spread to zero when only the two offsets are given")
step("parse the minimal legal shadow: two offsets and a colour")
val r = parse_box_shadow("1px 2px black")

step("the two omitted lengths are the CSS initial 0, not garbage")
match r:
    Ok(layers):
        expect(layers[0 as i32].blur).to_equal(0.0)
        expect(layers[0 as i32].spread).to_equal(0.0)
    Err(m):
        expect(m).to_equal("")
```

</details>

#### keeps comma-separated layers in source order

- keeps comma-separated layers in source order
- parse a two-layer shadow
- layer 0 is the first-authored one, which CSS paints on top
   - Expected: layers.len() equals `2`
   - Expected: layers[0 as i32].offset_x equals `1.0`
   - Expected: layers[0 as i32].color.r equals `255`
   - Expected: layers[1 as i32].offset_x equals `5.0`
   - Expected: layers[1 as i32].color.b equals `255`
   - Expected: m equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps comma-separated layers in source order")
step("parse a two-layer shadow")
val r = parse_box_shadow("1px 1px red, 5px 5px blue")

step("layer 0 is the first-authored one, which CSS paints on top")
match r:
    Ok(layers):
        expect(layers.len()).to_equal(2)
        expect(layers[0 as i32].offset_x).to_equal(1.0)
        expect(layers[0 as i32].color.r).to_equal(255)
        expect(layers[1 as i32].offset_x).to_equal(5.0)
        # `blue` is #0000FF.
        expect(layers[1 as i32].color.b).to_equal(255)
    Err(m):
        expect(m).to_equal("")
```

</details>

#### survives a colour function containing commas

- survives a colour function containing commas
- parse a shadow whose colour is rgba(), whose commas are nested
- the value is ONE layer, not four split on the inner commas
   - Expected: layers.len() equals `1`
   - Expected: layers[0 as i32].color.a equals `128`
   - Expected: m equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("survives a colour function containing commas")
step("parse a shadow whose colour is rgba(), whose commas are nested")
val r = parse_box_shadow("0 0 4px rgba(0, 0, 0, 0.5)")

step("the value is ONE layer, not four split on the inner commas")
match r:
    Ok(layers):
        expect(layers.len()).to_equal(1)
        # 0.5 alpha scaled to a byte and rounded: 0.5*255 = 127.5 -> 128.
        expect(layers[0 as i32].color.a).to_equal(128)
    Err(m):
        expect(m).to_equal("")
```

</details>

#### reads the inset keyword in either position

- reads the inset keyword in either position
- parse an inset shadow
- the keyword is recorded rather than dropped
   - Expected: layers[0 as i32].inset is true
   - Expected: m equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads the inset keyword in either position")
step("parse an inset shadow")
val r = parse_box_shadow("inset 0 0 2px red")

step("the keyword is recorded rather than dropped")
match r:
    Ok(layers):
        expect(layers[0 as i32].inset).to_equal(true)
    Err(m):
        expect(m).to_equal("")
```

</details>

#### reports `none` as an empty layer list rather than a failure

- reports `none` as an empty layer list rather than a failure
- parse the CSS initial value
- `none` is a legal value meaning zero shadows
   - Expected: layers.len() equals `0`
   - Expected: m equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports `none` as an empty layer list rather than a failure")
step("parse the CSS initial value")
val r = parse_box_shadow("none")

step("`none` is a legal value meaning zero shadows")
match r:
    Ok(layers):
        expect(layers.len()).to_equal(0)
    Err(m):
        expect(m).to_equal("")
```

</details>

#### fails on a single offset because CSS requires two

- fails on a single offset because CSS requires two
- parse a shadow with one length
- this is an error, not a shadow with a guessed second offset
   - Expected: r.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails on a single offset because CSS requires two")
step("parse a shadow with one length")
val r = parse_box_shadow("4px red")

step("this is an error, not a shadow with a guessed second offset")
expect(r.is_ok()).to_equal(false)
```

</details>

#### fails on a unit it cannot resolve without font context

- fails on a unit it cannot resolve without font context
- parse a shadow measured in em
- em would need a font size this leaf does not carry, so it errors rather than silently meaning 0px
   - Expected: r.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails on a unit it cannot resolve without font context")
step("parse a shadow measured in em")
val r = parse_box_shadow("1em 1em red")

step("em would need a font size this leaf does not carry, so it errors rather than silently meaning 0px")
expect(r.is_ok()).to_equal(false)
```

</details>

#### fails on an unknown colour keyword instead of substituting black

- fails on an unknown colour keyword instead of substituting black
- parse a shadow with a colour name that does not exist
- the historic silent-black bug would have made this succeed
   - Expected: r.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails on an unknown colour keyword instead of substituting black")
step("parse a shadow with a colour name that does not exist")
val r = parse_box_shadow("1px 1px notacolour")

step("the historic silent-black bug would have made this succeed")
expect(r.is_ok()).to_equal(false)
```

</details>

### parse_transform

#### turns translate into the matching affine translation

- turns translate into the matching affine translation
- parse a two-axis translate
- translation lands in the e/f column; the linear part stays identity
   - Expected: t.a equals `1.0`
   - Expected: t.d equals `1.0`
   - Expected: t.e equals `10.0`
   - Expected: t.f equals `20.0`
   - Expected: m equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("turns translate into the matching affine translation")
step("parse a two-axis translate")
val r = parse_transform("translate(10px, 20px)")

step("translation lands in the e/f column; the linear part stays identity")
match r:
    Ok(t):
        expect(t.a).to_equal(1.0)
        expect(t.d).to_equal(1.0)
        expect(t.e).to_equal(10.0)
        expect(t.f).to_equal(20.0)
    Err(m):
        expect(m).to_equal("")
```

</details>

#### applies a one-argument scale to both axes

- applies a one-argument scale to both axes
- parse a uniform scale
- CSS says scale(s) means scale(s, s), so both diagonal entries are 2
   - Expected: t.a equals `2.0`
   - Expected: t.d equals `2.0`
   - Expected: m equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies a one-argument scale to both axes")
step("parse a uniform scale")
val r = parse_transform("scale(2)")

step("CSS says scale(s) means scale(s, s), so both diagonal entries are 2")
match r:
    Ok(t):
        expect(t.a).to_equal(2.0)
        expect(t.d).to_equal(2.0)
    Err(m):
        expect(m).to_equal("")
```

</details>

#### composes a transform list left-to-right

- composes a transform list left-to-right
- parse translate followed by scale
- a point at x=1 maps to 10 + 2*1 = 12, so the translation is NOT scaled
   - Expected: p.0 equals `12.0`
   - Expected: t.a equals `2.0`
   - Expected: t.e equals `10.0`
   - Expected: m equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("composes a transform list left-to-right")
step("parse translate followed by scale")
val r = parse_transform("translate(10px, 0px) scale(2)")

step("a point at x=1 maps to 10 + 2*1 = 12, so the translation is NOT scaled")
match r:
    Ok(t):
        val p = t.apply(1.0, 0.0)
        expect(p.0).to_equal(12.0)
        # The scale still shows in the linear part.
        expect(t.a).to_equal(2.0)
        expect(t.e).to_equal(10.0)
    Err(m):
        expect(m).to_equal("")
```

</details>

<details>
<summary>Advanced: reads a 90-degree rotation as an exactly axis-aligned matrix</summary>

#### reads a 90-degree rotation as an exactly axis-aligned matrix

- reads a 90-degree rotation as an exactly axis-aligned matrix
- parse a quarter turn
- cos(90deg)=0 and sin(90deg)=1, so the point (1,0) maps to (0,1)
   - Expected: p.0 < 0.000000001 and p.0 > 0.0 - 0.000000001 is true
   - Expected: p.1 > 0.999999999 and p.1 < 1.000000001 is true
   - Expected: m equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads a 90-degree rotation as an exactly axis-aligned matrix")
step("parse a quarter turn")
val r = parse_transform("rotate(90deg)")

step("cos(90deg)=0 and sin(90deg)=1, so the point (1,0) maps to (0,1)")
match r:
    Ok(t):
        val p = t.apply(1.0, 0.0)
        # The series evaluation is not bit-exact, so assert to 1e-9 —
        # far tighter than any pixel could distinguish.
        expect(p.0 < 0.000000001 and p.0 > 0.0 - 0.000000001).to_equal(true)
        expect(p.1 > 0.999999999 and p.1 < 1.000000001).to_equal(true)
    Err(m):
        expect(m).to_equal("")
```

</details>


</details>

<details>
<summary>Advanced: reads matrix() entries in CSS a,b,c,d,e,f order</summary>

#### reads matrix() entries in CSS a,b,c,d,e,f order

- reads matrix() entries in CSS a,b,c,d,e,f order
- parse an explicit matrix
- each argument lands in its named slot
   - Expected: t.a equals `1.0`
   - Expected: t.b equals `2.0`
   - Expected: t.c equals `3.0`
   - Expected: t.d equals `4.0`
   - Expected: t.e equals `5.0`
   - Expected: t.f equals `6.0`
   - Expected: m equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads matrix() entries in CSS a,b,c,d,e,f order")
step("parse an explicit matrix")
val r = parse_transform("matrix(1, 2, 3, 4, 5, 6)")

step("each argument lands in its named slot")
match r:
    Ok(t):
        expect(t.a).to_equal(1.0)
        expect(t.b).to_equal(2.0)
        expect(t.c).to_equal(3.0)
        expect(t.d).to_equal(4.0)
        expect(t.e).to_equal(5.0)
        expect(t.f).to_equal(6.0)
    Err(m):
        expect(m).to_equal("")
```

</details>


</details>

<details>
<summary>Advanced: reports `none` as the identity matrix</summary>

#### reports `none` as the identity matrix

- reports `none` as the identity matrix
- parse the CSS initial value
- identity maps every point to itself
   - Expected: p.0 equals `7.0`
   - Expected: p.1 equals `9.0`
   - Expected: m equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports `none` as the identity matrix")
step("parse the CSS initial value")
val r = parse_transform("none")

step("identity maps every point to itself")
match r:
    Ok(t):
        val p = t.apply(7.0, 9.0)
        expect(p.0).to_equal(7.0)
        expect(p.1).to_equal(9.0)
    Err(m):
        expect(m).to_equal("")
```

</details>


</details>

#### fails on a 3D function rather than dropping the third axis

- fails on a 3D function rather than dropping the third axis
- parse translate3d
- silently discarding the z term would be a wrong transform, so this errors
   - Expected: r.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails on a 3D function rather than dropping the third axis")
step("parse translate3d")
val r = parse_transform("translate3d(1px, 2px, 3px)")

step("silently discarding the z term would be a wrong transform, so this errors")
expect(r.is_ok()).to_equal(false)
```

</details>

#### fails on an angle unit it does not support

- fails on an angle unit it does not support
- parse a rotation in radians
- treating rad as deg would be off by a factor of 57, so it errors
   - Expected: r.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails on an angle unit it does not support")
step("parse a rotation in radians")
val r = parse_transform("rotate(1rad)")

step("treating rad as deg would be off by a factor of 57, so it errors")
expect(r.is_ok()).to_equal(false)
```

</details>

### parse_linear_gradient

#### defaults an undirected gradient to `to bottom` and spreads stops evenly

- defaults an undirected gradient to `to bottom` and spreads stops evenly
- parse a three-stop gradient with no direction and no positions
- CSS's default gradient direction is to-bottom, which is 180deg
   - Expected: g.angle_deg equals `180.0`
   - Expected: g.stops.len() equals `3`
   - Expected: g.stops[0 as i32].position equals `0.0`
   - Expected: g.stops[1 as i32].position equals `0.5`
   - Expected: g.stops[2 as i32].position equals `1.0`
   - Expected: m equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("defaults an undirected gradient to `to bottom` and spreads stops evenly")
step("parse a three-stop gradient with no direction and no positions")
val r = parse_linear_gradient("linear-gradient(red, green, blue)")

step("CSS's default gradient direction is to-bottom, which is 180deg")
match r:
    Ok(g):
        expect(g.angle_deg).to_equal(180.0)
        expect(g.stops.len()).to_equal(3)
        # n=3 stops distribute at k/(n-1): 0, 0.5, 1.
        expect(g.stops[0 as i32].position).to_equal(0.0)
        expect(g.stops[1 as i32].position).to_equal(0.5)
        expect(g.stops[2 as i32].position).to_equal(1.0)
    Err(m):
        expect(m).to_equal("")
```

</details>

#### reads an explicit angle

- reads an explicit angle
- parse a 45-degree gradient
- the angle is kept verbatim; whether it can be PAINTED is a separate concern
   - Expected: g.angle_deg equals `45.0`
   - Expected: m equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads an explicit angle")
step("parse a 45-degree gradient")
val r = parse_linear_gradient("linear-gradient(45deg, red, blue)")

step("the angle is kept verbatim; whether it can be PAINTED is a separate concern")
match r:
    Ok(g):
        expect(g.angle_deg).to_equal(45.0)
    Err(m):
        expect(m).to_equal("")
```

</details>

#### maps a `to <side>` keyword to its CSS gradient angle

- maps a `to <side>` keyword to its CSS gradient angle
- parse a to-right gradient
- CSS gradient angles are clockwise from up, so `to right` is 90deg
   - Expected: g.angle_deg equals `90.0`
   - Expected: m equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("maps a `to <side>` keyword to its CSS gradient angle")
step("parse a to-right gradient")
val r = parse_linear_gradient("linear-gradient(to right, red, blue)")

step("CSS gradient angles are clockwise from up, so `to right` is 90deg")
match r:
    Ok(g):
        expect(g.angle_deg).to_equal(90.0)
    Err(m):
        expect(m).to_equal("")
```

</details>

#### keeps an authored stop position instead of redistributing it

- keeps an authored stop position instead of redistributing it
- parse a gradient whose middle stop is pinned at 25%
- the pinned stop stays at 0.25 while the unpinned ends stay at 0 and 1
   - Expected: g.stops[0 as i32].position equals `0.0`
   - Expected: g.stops[1 as i32].position equals `0.25`
   - Expected: g.stops[2 as i32].position equals `1.0`
   - Expected: m equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps an authored stop position instead of redistributing it")
step("parse a gradient whose middle stop is pinned at 25%")
val r = parse_linear_gradient("linear-gradient(red, green 25%, blue)")

step("the pinned stop stays at 0.25 while the unpinned ends stay at 0 and 1")
match r:
    Ok(g):
        expect(g.stops[0 as i32].position).to_equal(0.0)
        expect(g.stops[1 as i32].position).to_equal(0.25)
        expect(g.stops[2 as i32].position).to_equal(1.0)
    Err(m):
        expect(m).to_equal("")
```

</details>

#### parses colour functions inside stops without splitting on their commas

- parses colour functions inside stops without splitting on their commas
- parse a gradient whose stops are rgb() functions
- two stops, not six
   - Expected: g.stops.len() equals `2`
   - Expected: g.stops[0 as i32].color.r equals `255`
   - Expected: g.stops[1 as i32].color.b equals `255`
   - Expected: m equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses colour functions inside stops without splitting on their commas")
step("parse a gradient whose stops are rgb() functions")
val r = parse_linear_gradient("linear-gradient(rgb(255, 0, 0), rgb(0, 0, 255))")

step("two stops, not six")
match r:
    Ok(g):
        expect(g.stops.len()).to_equal(2)
        expect(g.stops[0 as i32].color.r).to_equal(255)
        expect(g.stops[1 as i32].color.b).to_equal(255)
    Err(m):
        expect(m).to_equal("")
```

</details>

#### fails on a one-stop gradient because a gradient needs two ends

- fails on a one-stop gradient because a gradient needs two ends
- parse a gradient with a single colour
- there is nothing to interpolate towards, so this is an error not a solid fill
   - Expected: r.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails on a one-stop gradient because a gradient needs two ends")
step("parse a gradient with a single colour")
val r = parse_linear_gradient("linear-gradient(red)")

step("there is nothing to interpolate towards, so this is an error not a solid fill")
expect(r.is_ok()).to_equal(false)
```

</details>

#### fails on radial-gradient rather than treating it as linear

- fails on radial-gradient rather than treating it as linear
- parse a radial gradient
- a different gradient shape is unsupported, not a linear one
   - Expected: r.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails on radial-gradient rather than treating it as linear")
step("parse a radial gradient")
val r = parse_linear_gradient("radial-gradient(red, blue)")

step("a different gradient shape is unsupported, not a linear one")
expect(r.is_ok()).to_equal(false)
```

</details>

#### fails on an unknown colour in a stop instead of substituting black

- fails on an unknown colour in a stop instead of substituting black
- parse a gradient with a bogus colour name
- same anti-silent-black contract as box-shadow
   - Expected: r.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails on an unknown colour in a stop instead of substituting black")
step("parse a gradient with a bogus colour name")
val r = parse_linear_gradient("linear-gradient(red, notacolour)")

step("same anti-silent-black contract as box-shadow")
expect(r.is_ok()).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-BLINK-PAINT-EFFECTS-001`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ef9a9994d033654e8ba19593951b363357f3576976ea7e1345b2fd50699ced3d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ef9a9994d033654e8ba19593951b363357f3576976ea7e1345b2fd50699ced3d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ef9a9994d033654e8ba19593951b363357f3576976ea7e1345b2fd50699ced3d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/blink/paint/effects_spec.spl
mirror: doc/06_spec/01_unit/lib/blink/paint/effects_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/lib/blink/paint/effects_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/blink/paint/effects_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/blink/paint/effects_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 49 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/blink/paint/effects_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/blink/paint/effects_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads offset, blur, spread and colour from a full four-length layer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/blink/paint/effects_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defaults blur and spread to zero when only the two offsets are given' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/blink/paint/effects_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps comma-separated layers in source order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
