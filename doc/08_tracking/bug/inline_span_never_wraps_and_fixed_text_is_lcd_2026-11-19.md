# A `<span>` wider than its line never wraps; `position:fixed` text paints LCD where Chrome paints grayscale

- **Found:** 2026-11-19, measuring bare text in positioned boxes against Chrome 159.
- **Status:** open, both.
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
