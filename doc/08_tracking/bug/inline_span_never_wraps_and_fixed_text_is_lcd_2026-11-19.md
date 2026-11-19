# A `<span>` wider than its line never wraps; `position:fixed` text paints LCD where Chrome paints grayscale

- **Found:** 2026-11-19, measuring bare text in positioned boxes against Chrome 159.
- **Status:** section 1 open; section 2 (fixed-text grayscale) resolved 2026-11-19 (`fixed_position_grayscale_text_chrome159_spec`).
- Pages: `body{margin:0;background:#fff;font:16px Liberation Sans;color:#000}`, text `Hamburgefonstiv Qy`, 400x120, `cpu_simd`. Ink = a channel under 200; fringe = red and blue more than 16 apart; mismatch = pixels with a channel more than 8 from Chrome.

## 1. Inline element text is one unbreakable box

| page | Chrome ink bbox | here |
|---|---|---|
| `<div style="width:90px;margin:30px 0 0 20px"><span>Hamburgefonstiv Qy</span></div>` | 20,32..140,64 (two lines) | 21,32..165,46 (one line), mismatch 618 |
| same box, absolutely positioned | 20,32..140,64 | 21,32..165,46, mismatch 618 |
| same box, text in a `<p>` or bare | 20,32..140,64 | 20,32..140,64, mismatch 357 |
| `<span>aa bb cc dd ee ff gg hh ii</span>` in the 90 px box | wraps | one line, ink to x 193 |
| `aa bb <span>cc dd ee ff gg</span> hh ii` | wraps inside the span | breaks before and after the span only, ink to x 158 |

A line breaks between inline items but never inside an inline element's text.

## 2. `position:fixed` text without an opaque background

| page | Chrome fringe pixels | here | mismatch |
|---|---|---|---|
| `<div style="position:fixed;left:20px;top:30px">` + text | 0 (grayscale) | 934 | 1084 |
| same with `background:#fff` | 970 (LCD) | 934 | 356 |
| `position:absolute` | 970 (LCD) | 934 | 357 |

Chrome gives a fixed box its own layer and draws LCD text only where the layer is opaque behind it. LCD is a per-frame switch here (`Engine2D.set_lcd_text`), so a per-run decision needs a flag on the Draw IR text command.

### Resolution of section 2 (2026-11-19)

Chrome 159 measured: fixed with no background, `rgba(255,255,255,.5)` or `#fff0` is grayscale (fringe 0); fixed with `background:#fff`, an opaque `<span>`/`<div>` background on a child, `position:absolute` and `position:sticky` are LCD (970). The Draw IR text command now carries `text-lcd:0` when no element from the text up to its `position:fixed` ancestor has an opaque background (`_html_draw_ir_fixed_gray_text`), and the executor sets LCD per text command. Pinned by `test/01_unit/browser_engine/fixed_position_grayscale_text_chrome159_spec.spl`.

### Resolution of section 1, partial (2026-11-19)

Root cause: in the block line loop (`simple_web_html_layout_renderer_layout_engine.spl`, the `if nodes[c].tag == "#text" and (not cst.white_space_nowrap ...)` arm that sets `inline_w = avail_inline`), only a `#text` child had its predicted box width clamped to the line. A plain inline element got `inline_w = intrinsic_text_width` (the whole unwrapped text) and was laid out at that width, so its nested #text never wrapped. Fix: the same clamp for a plain inline element that opens its line (`inline_x == inline_start_x`, not nowrap/pre). Chrome 159 (120 px div): span, span with `padding:0 4px`+background, and `<span><b>..</b>..</span>` all h=36; nowrap h=18; pinned by `inline_span_wrap_chrome159_spec`. Still open: (a) a span starting mid-line and longer than the remainder (`one <span>alpha beta gamma delta epsilon zeta</span> two`: Chrome h=54, fragments x=31.14/0/0; here h=36); (b) per-fragment background/padding (Chrome paints each fragment, padding only on first/last; here one rect).
