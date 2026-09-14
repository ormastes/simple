# A single non-ASCII codepoint sent a whole text run to the flat wrap estimate (2026-09-14)

Status: FIXED (round 16). Two defects, one substrate cause.

## Symptom

Every catalog `<li>` whose label carries an `&mdash;` measured one line box too
tall, and every box after it inherited the 24 px step, so a page accumulated
vertical drift proportional to how many such constructs preceded a given
element. Measured on `css-layout` before the fix, the `<body>` row was
`dh=697` and root `dy` values ran to 697; `css-paint` mismatched 516 of 529
compared elements.

The em dash was the trigger, not the `<code>` element the first fixtures
suspected. The decisive pair, in one 728 px block at 16px/1.5 sans-serif:

| run | Chrome | Simple before |
|---|---|---|
| `<code>align-content</code> — partial; values=keyword-number; owner=…spl` | 48 | 72 |
| `<code>align-content</code> xx partial; values=keyword-number; owner=…spl` | 48 | 48 |

Two characters of the same width, one ASCII and one not.

## Root cause

The text API in this engine is **mixed**, and this is the substrate the two
defects grew from — verified directly (`"a—b"`):

```
len=5                      # BYTES
char_code_at(0)=97  char_at(0)=a    # CODEPOINT-indexed
char_code_at(1)=8212 char_at(1)=—
char_code_at(2)=98  char_at(2)=b
char_code_at(3)=0   char_code_at(4)=0
substring(1,3) = <invalid utf-8>    # BYTE-indexed
```

So `len()`/`substring()` are byte-indexed while `char_code_at()`/`char_at()`
are codepoint-indexed, and the two coincide only on ASCII.

1. **`_lay_compute_style_wrap_ranges_inner`** gated the measured-advance path on
   `st.resolved_font_advances.len() != txt.len()` — one advance per CODEPOINT
   compared against a BYTE count. One em dash (3 bytes, 1 codepoint) made them
   disagree, so the whole wrap fell back to `compute_wrap_ranges`, the flat
   cells-per-line estimate (`style_char_w` = 12 px at font-size 16, against a
   real ~7.8 px average for this face). Being ~50 % too wide, it wrapped such a
   run one line early. The float-band twin
   `compute_style_wrap_ranges_float_band` carried the identical check.

2. **`style_run_byte_advances`** — the byte-indexed table that exists to answer
   exactly this, added in round 12 for the paint/layout advance disagreement —
   was itself **dead on non-ASCII**. It expanded codepoints to bytes by
   classifying `s.char_code_at(i)` as a UTF-8 lead or continuation byte, but
   `char_code_at` decodes and never returns a value in 128..191, so no
   continuation byte was ever recognised, `ci` over-ran the advance array on the
   first multi-byte codepoint, and the function returned an EMPTY array. Layout
   and paint then fell back together, silently, which is why fixing (1) alone
   changed nothing.

Defect (2) hid defect (1): the helper that would have fixed the guard was
itself broken by the same index confusion.

## Fix

`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl`

- `_lay_style_run_byte_advances_inner` expands from the CODEPOINT VALUES via a
  new `utf8_encoded_len`, and fails closed if the expansion does not total the
  string's byte length.
- both wrap loops gate on the byte table's own length, index it with the byte
  offsets they already use, test for a space through `txt.bytes()` (the space
  test was the same byte-vs-codepoint mix, so a break landed some bytes away
  from the space it meant to break at), and force progress through a new
  `next_codepoint_start` so a degenerate step cannot split a codepoint.

`…_paint_primitives.spl`: `fb_text_thin_scaled_clip_range_adv` walks bytes for
`by[i]` but had been reading the glyph with `char_code_at(i)`. That mix was
unreachable while the table was always empty on non-ASCII; making the table live
made it reachable, so the loop now carries its own codepoint cursor and draws
nothing for a continuation byte.

## Measured

Geometry differ, one tree / one binary (`2d066932…`) / one Chrome, toggling only
this change:

| page | compared | before | after |
|---|---|---|---|
| css-paint | 529 | 516 | **9** |
| css-layout | 402 | 337 | 378 |
| html | 432 | 230 | 230 |

`css-layout`'s COUNT rose while its geometry improved four-fold: root `dy`
values fall from a 697 px maximum to 169 px. The residual is a different,
still-open defect (below) that the old over-wide estimate was accidentally
compensating for in the opposite direction.

Spec: `test/01_unit/browser_engine/non_ascii_run_wrap_byte_advances_spec.spl`,
6/6, each defect sabotage-proven separately, with the ASCII twin as a control
that must NOT move.

## Left open, named rather than guessed at

- **A `#text` node that starts at a non-zero pen x wraps at the FULL container
  width.** Each `#text` node is wrapped independently against `node_w`
  (`…_layout.spl` `#text` branch), so an inline sibling before it — `<code>`,
  `<span>` — does not reduce the first line's available width. Fixture:
  `<div style="width:728px"><code>align-content</code> — partial;
  values=keyword-number; owner=simple_web_html_layout_renderer_layout.spl</div>`
  is 88 px in Chrome for the `<li>` shape and 64 px in Simple. This is now the
  dominant `css-layout` residual and is an inline-packing question, not a
  measurement one.
- `resolved_text_range_width` (`…_layout.spl`) still indexes the codepoint
  advance array with byte offsets; it is used only by the ellipsize path and is
  deliberately left for a lane that can measure that path.
- `fb_text_thin_scaled_clip_range` (the flat fallback stepper) carries the same
  byte-range / codepoint-index mix, pre-existing and untouched.
