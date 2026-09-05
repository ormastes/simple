# `tools/layout_diff` — Chrome ↔ Simple component-level layout differential

Feeds the same HTML fixture to Chrome and to Simple's web renderer, extracts the
same intermediate artifact from each (stage 3 box geometry, stage 4 line boxes),
normalizes, and diffs numerically. Not a screenshot comparison.

| File | Role |
|---|---|
| `CONTRACT.md` | I/O contract per stage, normalization rules, node-pairing strategy |
| `fixtures/*.html` | 18 fixtures, one layout behavior each |
| `chrome_layout_dump.js` | CDP extractor (`DOMSnapshot.captureSnapshot`, `includeTextBoxes: true`) |
| `simple_layout_dump.spl` | Simple extractor (real `layout()` pipeline → JSON) |
| `layout_diff.js` | numeric differ → `out/report.json`, `out/summary.txt` |
| `run_layout_diff.shs` | fail-closed driver (~4 min) |

```sh
sh tools/layout_diff/run_layout_diff.shs --chrome <path>
bin/simple test test/03_system/browser_engine/chrome_layout_differential_spec.spl
```

Exit codes: `0` no divergence, `1` divergences, `3` nothing compared (vacuous),
`4` no Chrome found. `3` and `4` are failures, never passes.

---

## Recorded baseline — Chrome 151.0.7922.34, 800×600, dSF 1

```
fixtures_compared=18  nodes_compared=96  text_nodes_compared=10
findings_total=75     unpaired=0         fixtures_missing=0
max_geom_delta=234.78 css px
```

**Pure block layout is exact; every divergence is downstream of text measurement,
or is the float implementation.** 8 of 18 fixtures are byte-identical at
ε = 0.5 px: `01_block_stacking`, `02_margin_collapse`, `03_padding_border`,
`04_box_sizing_border`, `05_nested_offsets`, `15_width_percent`,
`16_margin_auto`, `18_nested_block_height` — i.e. sibling stacking, adjacent
margin collapse, content-box padding/border expansion, `box-sizing: border-box`,
3-level nested padding offsets, nested percentage widths, `margin: auto`
centering, and parent-height-from-children all agree with Blink to the pixel.

### Which line breaker is actually wired

The **CPU** one. `compute_style_wrap_ranges` (`..._layout.spl:642`) →
`compute_wrap_ranges` (`:618`) → `wrap_line_end` (`:529`), greedy
last-space-before-limit. `gpu_web/text/cuda_line_break.spl` (PTX
`web_line_break_latin`) is reached only through
`simple_web_render_session.spl:358` → `gpu_web/layout/manager.spl:115`, emits a
`WebGpuLineBreakProof` compared against the CPU oracle, and **never writes back
geometry** — it is verification, not layout. Nothing under `skia/feature/shaper`
breaks lines; the shaper only supplies advances. Two breakers exist, one is
authoritative: fixing a wrap bug in the CUDA kernel changes nothing.

### Root cause of the text divergences: shaping fails, advances are synthetic

Every extraction logs `[rfm] at=measure shaped_valid=false` while
`has_ttf=true`. A font is bound and the shaper is called, but it returns invalid
shaping on every fixture, so measurement falls back to the synthetic ladder at
`..._layout.spl:285/290/313` (`char_w = 6*glyph_scale`,
`glyph_scale = max(1, fs/8)`).

| fixture | font-size | Chrome break | Simple break |
|---|---|---|---|
| `06_inline_wrap` | 16px | after 19 chars | after 19 chars |
| `14_font_size_wrap` | **24px** | after **11** chars | after **19** chars |

Simple breaks at the same character count for a 16px and a 24px font in a 200px
box — the wrap advance is font-size-invariant. At 16px the ladder is accidentally
near monospace (Chrome 9.85 px/char vs Simple ~10.5), which is why 16px looks
almost right; at 24px Chrome is 14.4 px/char and Simple is still ~10.5, so the
line overflows by 78%.

### Worst-first divergences

**1. Unbreakable word hard-chopped instead of overflowing** — `07_long_word`
```
LINE_COUNT  chrome=2  simple=4
line 0  chrome="supercalifragilisticexpialidocious"  simple="supercalif"
line 1  chrome="tail"                                simple="ragilistic"
GEOM_W  chrome=334.78  simple=100  delta=-234.78 px   <-- largest single delta
GEOM_H  chrome=40      simple=64   delta=+24
```
CSS says a word with no break opportunity overflows its box. Simple chops every
10 characters. Wrong rule, not a rounding difference — and the text node's width
is then reported as the container (100) rather than the real content width
(334.78), so intrinsic-width consumers get a wrong answer too.

**2. `text-align: center` not applied to inline content** — `09_text_align_center`
```
GEOM_X  #t/#text[0]  chrome=61.375  simple=0  delta=-61.375 px
```
The containing block matches; the text sits flush left. Simple has no per-line
rect, so alignment has nowhere to be expressed.

**3. Float not taken out of flow** — `11_float_left`
```
#after  GEOM_Y  chrome=0   simple=40   delta=+40
#body   GEOM_H  chrome=60  simple=100  delta=+40
```
Chrome floats the 40px block out of flow (`#after` at y=0, body 60 tall). Simple
stacks it as an ordinary block. A `FloatContext` is threaded through `layout`,
so the plumbing exists; the offset is not consumed.

**4. CJK breaks early then stops limiting width** — `13_cjk_wrap`
```
LINE_COUNT  chrome=3  simple=2
line 0  chrome="日本語のテキス" (7)  simple="日本語のテ" (5)
line 1  chrome="トは空白なしで" (7)  simple="キストは空白なしで折り返します" (15)
GEOM_H  chrome=63  simple=32  delta=-31
```
Simple does break CJK without spaces (so the Latin-only fast path is not the one
running), but fits 5 where Chrome fits 7, then emits the whole 15-character
remainder as one line overflowing the 120px box — the width limit stops being
applied after the first break.

**5. Inline x drift accumulates** — `12_inline_elements`
```
#s2  GEOM_X  chrome=59.094   simple=51   delta=-8.09
#s3  GEOM_X  chrome=128.031  simple=112  delta=-16.03
```
Per-span width error is 0.77–0.92 px but compounds to 16 px by the third span.
This is why ε cannot simply be raised to hide the text findings.

**6. Line box model / leading** — `10_line_height`, all wrapped text
```
10_line_height  GEOM_Y  chrome=6   simple=0   delta=-6
10_line_height  GEOM_H  chrome=52  simple=64  delta=+12
06_inline_wrap  GEOM_H  chrome=40  simple=32  delta=-8
```
Chrome applies `line-height: 32px` as half-leading (first baseline pushed 6 px
down, union box 52); Simple emits 2 × 32 = 64 with no leading. At default
line-height Simple is 16 px/line against Chrome's 20 px/line.

**7. Ambient 2–4 px height deficit on any block containing text** —
`08_whitespace`, `09_text_align_center`, `12_inline_elements`,
`17_display_inline_block` report `html`/`body`/`div` heights short by 2–4 px
(20→18, 25→23), plus a 1 px `y` offset on text nodes in six fixtures. Same root
cause as (6).

### Fix priority

1. **`shaped_valid=false`** — one fix moves items 5, 6, 7 and half of 1–4 at
   once. Nothing else is worth doing first.
2. `overflow-wrap` for unbreakable words (item 1) — wrong rule.
3. Float out-of-flow (item 3) — wrong rule.
4. Per-line rects in `LayoutResult` — without them `text-align` and
   `line-height` cannot be *measured*, which is also what makes the stage-4
   oracle weaker than it should be.
5. CJK width limit after the first break (item 4).

The spec ratchets `findings_total <= 75`. Fixes should lower it; the baseline
must never be raised to accommodate a regression.
