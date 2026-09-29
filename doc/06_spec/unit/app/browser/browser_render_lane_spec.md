# Browser Render Lane: Choosing An Engine By Flag

> I maintain the Simple Browser. Two rendering engines exist in this repo: the live one that ships today, and the blink stack, which is better factored but still a functional subset. I need to be able to try blink in a real production call path without betting the product on it — and I need to be able to change my mind in one line if it goes wrong.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Render Lane: Choosing An Engine By Flag

I maintain the Simple Browser. Two rendering engines exist in this repo: the live one that ships today, and the blink stack, which is better factored but still a functional subset. I need to be able to try blink in a real production call path without betting the product on it — and I need to be able to change my mind in one line if it goes wrong.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink |
| Status | Active |
| Source | `test/unit/app/browser/browser_render_lane_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

I maintain the Simple Browser. Two rendering engines exist in this repo: the
live one that ships today, and the blink stack, which is better factored but
still a functional subset. I need to be able to try blink in a real production
call path without betting the product on it — and I need to be able to change
my mind in one line if it goes wrong.

So the browser now renders through an adapter,
`app.browser.render_lane`, that picks a lane by flag. Both lanes expose the
same `(html, width, height) -> [u32]` signature, so choosing between them is a
dispatch, not a fork in the calling code.

**The flag defaults to the live lane, and these examples hold it there.**
blink is not ready to be the default, and I would rather prove exactly where it
falls short than discover it in a screenshot. So this file does three things:

1. pins the default to the live lane, so wiring blink in changes nothing yet;
2. proves BOTH lanes really produce pixels through the adapter;
3. asserts blink's remaining gaps *as behaviour*, so the day one closes, the
   example that documents it goes red and someone updates the exit criteria in
   `render_lane.spl` instead of quietly shipping a regression.

@manual_section Browser Rendering

## Scenarios

### the render lane the browser actually uses

#### defaults to the live lane, so wiring blink in changes no rendering

- defaults to the live lane, so wiring blink in changes no rendering
- read the compiled-in default
   - Expected: BROWSER_RENDER_LANE_DEFAULT equals `BROWSER_RENDER_LANE_LIVE`
- read the lane this process will really render through
   - Expected: browser_render_lane_selected() equals `BROWSER_RENDER_LANE_LIVE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults to the live lane, so wiring blink in changes no rendering")
step("read the compiled-in default")
expect(BROWSER_RENDER_LANE_DEFAULT).to_equal(BROWSER_RENDER_LANE_LIVE)

step("read the lane this process will really render through")
# No SIMPLE_BROWSER_RENDER_LANE is set for the test runner, so the
# selection must fall through to the default. If this ever reports
# "blink", the seam has flipped the product without anyone deciding to.
expect(browser_render_lane_selected()).to_equal(BROWSER_RENDER_LANE_LIVE)
```

</details>

#### names both lanes as dispatchable and rejects anything else

- names both lanes as dispatchable and rejects anything else
- check the two real lane names
   - Expected: browser_render_lane_is_known(BROWSER_RENDER_LANE_LIVE) is true
   - Expected: browser_render_lane_is_known(BROWSER_RENDER_LANE_BLINK) is true
- check a typo and an empty value
   - Expected: browser_render_lane_is_known("blinkk") is false
   - Expected: browser_render_lane_is_known("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("names both lanes as dispatchable and rejects anything else")
step("check the two real lane names")
expect(browser_render_lane_is_known(BROWSER_RENDER_LANE_LIVE)).to_equal(true)
expect(browser_render_lane_is_known(BROWSER_RENDER_LANE_BLINK)).to_equal(true)

step("check a typo and an empty value")
# A mistyped env var must not be dispatchable, so selection falls back
# to the default rather than rendering through nothing.
expect(browser_render_lane_is_known("blinkk")).to_equal(false)
expect(browser_render_lane_is_known("")).to_equal(false)
```

</details>

#### exposes the override under a single documented env var name

- exposes the override under a single documented env var name
- read the env var name the adapter honours
   - Expected: BROWSER_RENDER_LANE_ENV equals `SIMPLE_BROWSER_RENDER_LANE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exposes the override under a single documented env var name")
step("read the env var name the adapter honours")
expect(BROWSER_RENDER_LANE_ENV).to_equal("SIMPLE_BROWSER_RENDER_LANE")
```

</details>

### both lanes produce real pixels through the adapter

#### renders a page through the live lane and returns a full buffer

- renders a page through the live lane and returns a full buffer
- render 4x2 pixels through the live lane
- the buffer holds one entry per pixel: 4 x 2 = 8
   - Expected: pixels.len() equals `LIVE_PIXELS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders a page through the live lane and returns a full buffer")
step("render 4x2 pixels through the live lane")
val pixels = render_html_to_pixel_array_via(
    BROWSER_RENDER_LANE_LIVE, "<html><body><p>Hi</p></body></html>",
    LIVE_W, LIVE_H)

step("the buffer holds one entry per pixel: 4 x 2 = 8")
expect(pixels.len()).to_equal(LIVE_PIXELS)
```

</details>

#### renders a page through the blink lane and paints the styled box

- renders a page through the blink lane and paints the styled box
- render a white 20x10 page holding one red 10x5 div
- the buffer holds one entry per pixel: 20 x 10 = 200
   - Expected: pixels.len() equals `VIEW_PIXELS`
- the div covers exactly its own 10 x 5 = 50 pixels in red
   - Expected: _count(pixels, RED) equals `50`
- the remaining 200 - 50 = 150 pixels are the white page behind it
   - Expected: _count(pixels, WHITE) equals `150`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders a page through the blink lane and paints the styled box")
step("render a white 20x10 page holding one red 10x5 div")
val pixels = _blink(_page("red"))

step("the buffer holds one entry per pixel: 20 x 10 = 200")
expect(pixels.len()).to_equal(VIEW_PIXELS)

step("the div covers exactly its own 10 x 5 = 50 pixels in red")
expect(_count(pixels, RED)).to_equal(50)

step("the remaining 200 - 50 = 150 pixels are the white page behind it")
expect(_count(pixels, WHITE)).to_equal(150)
```

</details>

#### primes the page white so an unpainted pixel is not transparent black

- primes the page white so an unpainted pixel is not transparent black
- render a page whose only styling is a white body
- all 200 pixels are opaque white, none left at the buffer's zero fill
   - Expected: _count(pixels, WHITE) equals `VIEW_PIXELS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("primes the page white so an unpainted pixel is not transparent black")
step("render a page whose only styling is a white body")
val pixels = _blink(
    "<html><body><style>body { background-color: white; " +
    "width: 20px; height: 10px; }</style></body></html>")

step("all 200 pixels are opaque white, none left at the buffer's zero fill")
# ChunkRasterBuffer.create zero-fills, which is transparent black. If
# the lane forgot to prime the canvas, this count would be 0 and every
# pixel would read as "painted" to the live lane's pixel counter.
expect(_count(pixels, WHITE)).to_equal(VIEW_PIXELS)
```

</details>

### where blink still differs from the live lane today

#### paints no text glyphs at all, which is the biggest blocker to the flip

- paints no text glyphs at all, which is the biggest blocker to the flip
- render a page whose only content is a paragraph of text
- every one of the 200 pixels is still blank page — no glyph was drawn
   - Expected: _count(pixels, WHITE) equals `VIEW_PIXELS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("paints no text glyphs at all, which is the biggest blocker to the flip")
step("render a page whose only content is a paragraph of text")
val pixels = _blink(
    "<html><body><style>body { background-color: white; " +
    "width: 20px; height: 10px; }</style><p>Hello</p></body></html>")

step("every one of the 200 pixels is still blank page — no glyph was drawn")
# blink's paint step (`paint_chunks_from_styled_layout`) emits one
# background rect per box and nothing else. The live lane draws the
# text. Until this example goes red, no consumer that needs readable
# page text can move to blink.
expect(_count(pixels, WHITE)).to_equal(VIEW_PIXELS)
```

</details>

#### ignores an inline style= attribute that the live lane would honour

- ignores an inline style= attribute that the live lane would honour
- render a div styled only by its own style= attribute
- not one of the 200 pixels is red: the attribute never reached the cascade
   - Expected: _count(pixels, RED) equals `0`
   - Expected: _count(pixels, WHITE) equals `VIEW_PIXELS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ignores an inline style= attribute that the live lane would honour")
step("render a div styled only by its own style= attribute")
val pixels = _blink(
    "<html><body><style>body { background-color: white; " +
    "width: 20px; height: 10px; }</style>" +
    "<div style=\"background-color: red; width: 10px; height: 5px\">" +
    "</div></body></html>")

step("not one of the 200 pixels is red: the attribute never reached the cascade")
# blink's CSS parser CAN read this (`parse_inline_style`), but
# `blink.style.cascade.resolve_style` consults only the stylesheet, so
# nothing feeds it in. Stated as behaviour rather than left to a
# comment, because the failure mode is a silently unstyled box.
expect(_count(pixels, RED)).to_equal(0)
expect(_count(pixels, WHITE)).to_equal(VIEW_PIXELS)
```

</details>

#### does resolve the full CSS colour set, so colour is no longer a blocker

- does resolve the full CSS colour set, so colour is no longer a blocker
- render the same 10 x 5 = 50 pixel box four different ways
   - Expected: _count(_blink(_page("red")), RED) equals `50`
   - Expected: _count(_blink(_page("rgb(255, 0, 0)")), RED) equals `50`
   - Expected: _count(_blink(_page("hsl(0, 100%, 50%)")), RED) equals `50`
   - Expected: _count(_blink(_page("#ff0000ff")), RED) equals `50`
- a CSS Level 4 name outside the old 9-name subset also resolves
   - Expected: _count(tomato, RED) equals `0`
   - Expected: _count(tomato, WHITE) equals `150`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does resolve the full CSS colour set, so colour is no longer a blocker")
step("render the same 10 x 5 = 50 pixel box four different ways")
# The wiring plan recorded blink as having ~9 named colours and no
# rgb()/hsl()/#RRGGBBAA. That gap has since been closed by delegating
# to `common.color.css.parse_css_color`, so all four spellings of
# opaque red must now paint the identical 50 pixels.
expect(_count(_blink(_page("red")), RED)).to_equal(50)
expect(_count(_blink(_page("rgb(255, 0, 0)")), RED)).to_equal(50)
expect(_count(_blink(_page("hsl(0, 100%, 50%)")), RED)).to_equal(50)
expect(_count(_blink(_page("#ff0000ff")), RED)).to_equal(50)

step("a CSS Level 4 name outside the old 9-name subset also resolves")
# `tomato` was not in blink's old table. It must now paint its own 50
# pixels — neither red, nor left as unpainted white page.
val tomato = _blink(_page("tomato"))
expect(_count(tomato, RED)).to_equal(0)
expect(_count(tomato, WHITE)).to_equal(150)
```

</details>

### the user-agent default stylesheet — exit criterion 5, partially closed

#### an <a> with no author colour rule paints its glyphs the UA default blue

- an <a> with no author colour rule paints its glyphs the UA default blue
- render a page whose only <a> styling is its own inline size
- some pixels are the UA sheet's default link blue, not the page's black initial colour
   - Expected: _count(pixels, BLUE) > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an <a> with no author colour rule paints its glyphs the UA default blue")
step("render a page whose only <a> styling is its own inline size")
val pixels = _blink(_link_page(""))

step("some pixels are the UA sheet's default link blue, not the page's black initial colour")
# `blink.style.cascade`'s CSS initial `color` is black — if the UA
# sheet were not reaching the cascade, these glyph pixels would come
# out black instead, and this count would be 0.
expect(_count(pixels, BLUE) > 0).to_equal(true)
```

</details>

#### sabotage check: an author `a { color: ... }` rule still overrides the UA default

- sabotage check: an author `a { color: ... }` rule still overrides the UA default
- render the same page, this time with an author rule for <a>'s colour
- no blue glyph pixels: the author rule beat the UA default, not the reverse
   - Expected: _count(pixels, BLUE) equals `0`
- red glyph pixels appear instead, proving text painted at all
   - Expected: _count(pixels, RED) > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sabotage check: an author `a { color: ... }` rule still overrides the UA default")
step("render the same page, this time with an author rule for <a>'s colour")
val pixels = _blink(_link_page("a { color: red; }"))

step("no blue glyph pixels: the author rule beat the UA default, not the reverse")
expect(_count(pixels, BLUE)).to_equal(0)
step("red glyph pixels appear instead, proving text painted at all")
expect(_count(pixels, RED) > 0).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b50a7da849adc884b3ae2de375b8070b40c54b17d9b9674d4e9c7bcc78902112`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b50a7da849adc884b3ae2de375b8070b40c54b17d9b9674d4e9c7bcc78902112`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b50a7da849adc884b3ae2de375b8070b40c54b17d9b9674d4e9c7bcc78902112`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/browser/browser_render_lane_spec.spl
mirror: doc/06_spec/unit/app/browser/browser_render_lane_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/browser/browser_render_lane_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/browser/browser_render_lane_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/browser/browser_render_lane_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/browser/browser_render_lane_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defaults to the live lane, so wiring blink in changes no rendering' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/browser/browser_render_lane_spec.spl:110:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'names both lanes as dispatchable and rejects anything else' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/browser/browser_render_lane_spec.spl:123:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes the override under a single documented env var name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
