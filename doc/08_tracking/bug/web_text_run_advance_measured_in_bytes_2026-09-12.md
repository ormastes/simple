# A non-ASCII text run wrapped to one line box per UTF-8 BYTE (FIXED)

- Status: FIXED 2026-09-12 (`simple_web_html_layout_renderer_layout.spl`,
  `style_measured_run_advance`)
- Area: `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl`
- Found by: round-4 catalog geometry work; isolated to a two-tag repro

## Repro (before the fix)

At 900 px, `body{margin:0;font:16px/1.5 sans-serif}`:

| page body | Chrome h | Simple h |
|---|---|---|
| `<div>&mdash;</div>` | 24 | **72** |
| `<div>&mdash; partial</div>` | 24 | **72** |
| `<div>caf&eacute; partial</div>` | 24 | **72** |
| `<div>- partial</div>` | 24 | 24 |

Any single non-ASCII codepoint tripled the block's height; a pure-ASCII run of
the same visible length was correct. 72 px is 3 line boxes — exactly the 3 UTF-8
bytes of `—`.

## Root cause

`resolved_font_advances` carries one advance per CODEPOINT. `txt_len` and every
wrap offset in this renderer are BYTE indices. On a non-ASCII run the two
disagree, `resolved_text_range_width` correctly bails to -1, and the flat
per-character estimate that replaced it was then compared against a `node_w`
that had already been sized from the REAL measured width. The run therefore
"overflowed" its own box, fell into `compute_style_wrap_ranges`, missed the
same arity check there, and wrapped with the byte-based fallback at
`cpl = node_w / char_w` = 1 — one byte per line.

## Fix

`style_measured_run_advance` returns the measured `resolved_font_width` when the
advance array's arity matches the run's CODEPOINT count, so the whole-run width
is compared against the box in the same units it was derived from. The run then
fits and stays on one line.

## Impact beyond the repro

Every catalog `<li>` whose text carries an `&mdash;` was 2 extra line-heights
tall; on `round4_probe.html` the list block went 152 -> 104 px (Chrome 104) and
the nested `<p>`'s y went 208 -> 160 (Chrome 160), both now exact.

## Still open (same units defect, narrower)

`compute_style_wrap_ranges` / `compute_wrap_ranges` still split on BYTE offsets
with a codepoint-keyed advance array, so a non-ASCII run that GENUINELY exceeds
its box still wraps at the wrong places. The fix above removes the common case
(runs that fit) but not that one.

## Pin

`test/01_unit/browser_engine/inline_run_advance_and_break_boxes_spec.spl`
AC-2/AC-3, `5 examples, 0 failures`. Sabotage: disabling the codepoint-arity
branch fails 2 of the 5.
