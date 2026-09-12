# Engine2D stages one text quad per BYTE against a per-CODEPOINT advance array — a single em dash renders the whole page black

- Status: FIXED in Engine2D / text staging (2026-09-12, branch
  `work/engine2d-text-staging-codepoints-2026-09-12`). The producer-side
  containment below is still in place and still correct -- both arities are now
  accepted -- and can be removed in a follow-up owned by the browser-engine
  lane. Round 5's diagnosis below is retained as the history. Round 5 landed a
  fail-safe guard on the PRODUCER side (browser engine) so affected pages render
  at all; that guard is a containment, not the fix.
- Area: `src/lib/gc_async_mut/gpu/engine2d/engine.spl:2072`
  (`Engine2D.draw_text_with_advances_*` ->
  `FontRenderer.stage_text_with_advances_configured`) and
  `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl:2207`

## Reproduction — clean `origin/main` @ `43cb44149fe`, no local edits

```
SIMPLE_BIN=<repo>/build/cargo-r2/release/simple \
sh scripts/check/check-chrome-catalog-pixel-diff.shs --out build/perf/r5_base
```

`build/perf/r5_base/html.simple.log` and `css-layout.simple.log` both end:

```
[e2d-batch] advances-draw-failed text='— renderable; values=element; owner=…'
            advances=71 batch_valid=false quads=68
[e2d-ir] draw-false shaped=0 payload_valid=1 advances=71 text_len=73 glyphs=0 size=16
render produced too few pixels: 0 < 684000
```

and

```
[e2d-ir] draw-false shaped=0 payload_valid=1 advances=82 text_len=84 glyphs=0 size=16
            text='— partial; values=keyword-number; owner=…'
render produced too few pixels: 0 < 684000
```

Two of the eight catalog pages produce **zero pixels**, so they cannot be
compared at all. Round 4 measured `html` at 17.05 % and `css-layout` at 29.19 %,
so this arrived between round 4 and PR #619.

## The arithmetic, which is the whole bug

`advances=71 text_len=73` and `advances=82 text_len=84`: a difference of exactly
2 on a string containing exactly one em dash. `U+2014` is 3 bytes of UTF-8 and 1
codepoint, so 3 - 1 = 2. `ResolvedFontMetrics.advances` carries **one advance per
codepoint** — this is explicit and deliberate in
`src/lib/nogc_sync_mut/text_layout/font_renderer.spl` (`val character_count =
text_codepoints(content).len()`; `valid = identity != "" and advances.len() ==
character_count`). The consumer walks **bytes**: `quads=68` for a 73-byte string
confirms the staging loop and the advance array run at different rates, the batch
is marked `batch_valid=false`, `draw_text_with_advances_*` returns false, and
Draw-IR gives up on the entire composition — not just that one run.

That last part is the reason this is severe rather than cosmetic: one em dash
anywhere on the page costs every pixel of the page.

## Containment landed in round 5 (producer side)

`_html_draw_ir_resolved_text_command` in
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_layout.spl`
now re-expresses the advance array in the CONSUMER's index space before handing
it over: `_html_draw_ir_byte_advances` emits the codepoint's advance on its lead
byte and 0 on each UTF-8 continuation byte, so the array has exactly `txt.len()`
entries and sums to the identical total width.

Dropping these runs to the flat estimate was considered and rejected: layout's
`inline_text_advance_width` matches on **trimmed codepoint** arity and therefore
keeps using the real metrics on exactly these runs, so a flat paint fallback
would have re-created the layout/paint disagreement this round exists to remove --
trading "renders nothing" for "renders wrong". The byte expansion keeps both
sides on the same numbers, and is a literal no-op on ASCII, where bytes and
codepoints coincide.

It is still a workaround for someone else's index space, and it stops being
needed the moment the consumer walks codepoints.

## When did it arrive

Round 4 measured `html` at 17.05 % and `css-layout` at 29.19 %, so both rendered
then. Round 4's own commit `a35ad52ed6f` touched only
`simple_web_html_layout_renderer_layout.spl`, its spec and its fixture -- it did
not change the metrics arity, so it is not the cause. The per-codepoint advance
contract in `font_renderer.spl` moved on the same day under two other lanes'
perf commits, `23ee4a2a496` ("the style stage's 90% was glyph advances, not the
cascade") and `3e06f6f9abd` ("the measurement residual was the cmap re-parse,
not kerning"); Engine2D's font staging moved under `c26ee7b3550`,
`360014cc729` and `519d46b8450`. Round 5 did NOT bisect these -- the candidates
are named from the file history alone so the next investigator has a starting
set, not a verdict.

## What would close it

Convert the staging loop to iterate codepoints (`text_codepoints`) so it consumes
the per-codepoint array it is handed, and add a fail-closed assertion at the
Engine2D boundary that `advances.len() == codepoint_count` rather than silently
returning false. Then remove the producer-side guard above and re-measure `html`
and `css-layout`, which should return to the round-4 figures or better.


## What actually failed, corrected (2026-09-12)

"The consumer walks bytes" was right about the INDEX SPACE and wrong about
where it diverged. `font_batch_apply_advances` did iterate per codepoint (its
`for ch in content` binding yields one entry per codepoint, which is why the
Draw IR gate counted 71 and the `[e2d-batch]` receipt fired at all), but it
built its lookup table from cumulative **byte** offsets, while the staged quads
carry a **codepoint index** in their field named `byte_offset`: both
`LayoutGlyph` producers in `font_renderer.spl` increment it by 1 per glyph. On
ASCII the two spaces are identical; after one em dash every
`_font_character_index` lookup missed, the function returned false, the batch
was marked invalid and the composition was dropped.

## The fix

- `src/lib/nogc_sync_mut/text_layout/font_advance_layout.spl`: decodes the run
  once with `text_codepoints`, indexes advances and shifts per codepoint, and
  resolves the quads' index space ONCE per batch (`codepoint_space`) instead of
  assuming byte offsets. New `font_advances_codepoint_arity` accepts BOTH
  conventions -- per-codepoint, and round 5's byte-expanded array, which it
  collapses losslessly -- and returns `[]` for anything else so the caller can
  fall back instead of reinterpreting.
- `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl`: the advance gate counts
  codepoints (`text_codepoints`) and normalises to codepoint arity; a producer
  may state which convention it sent with the `font-advance-arity` style prop
  ("codepoint" | "byte"), and a declaration that disagrees with what arrived
  takes the fallback rather than being silently reinterpreted. A resolved-text
  run that still cannot be staged is now PAINTED with the font's own advances
  and recorded via `mark_cpu_fallback("text-advance-arity")` -- it never drops
  the Draw IR. Shaped runs with a malformed payload stay fail-closed.
- `src/lib/gc_async_mut/gpu/engine2d/engine.spl`: `mark_cpu_fallback_reason`
  forwards a fallback receipt to the Vulkan backend when one is attached.

## Evidence

- `test/01_unit/lib/nogc_sync_mut/text_layout/font_advance_codepoint_arity_spec.spl`
  9 examples, 0 failures. Sabotage (force the byte index space): 9 examples,
  2 failures -- both em-dash examples, ASCII green.
- `test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_em_dash_text_ink_spec.spl`
  2 examples, 0 failures (cpu_simd, interpreter). Sabotage reproduces the
  incident signature exactly: `[e2d-ir] draw-false ... advances=23 text_len=25
  text='an em dash — renderable'` and zero ink, while the ASCII control passes.
- `scripts/check/check-chrome-catalog-pixel-diff.shs` now classifies a readable
  but inkless capture as `zero-pixel-render` and NAMES the page, instead of
  folding it into "unreadable". Keyed on the PPM, never on a log line.
  `--selftest`: `PASS — 5 selftest fixture(s) checked`.
- `draw_ir_adv_spec.spl`: 69 examples, 25 failures BOTH before and at
  origin/main -- a pre-existing red, unchanged by this work (verified by
  running the same file with the three edited sources restored to
  `origin/main`, offender lists byte-identical).

## Follow-up: producer switched to per-codepoint arity (2026-09-12)

Done. `_html_draw_ir_byte_advances` is replaced by
`_html_draw_ir_codepoint_advances` in
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_layout.spl`:
it validates `advances.len() == text_codepoint_len(txt)` and hands the canonical
per-codepoint array straight to `draw_ir_text_resolved_font` /
`draw_ir_text_shaped_font`, and the merged style props now declare
`font-advance-arity: codepoint`. A mis-sized array still returns `[]` so the run
takes the flat styled fallback rather than shipping a wrong-length array.

Parity is unchanged: the CPU framebuffer painter keeps its BYTE view
(`style_run_byte_advances`) derived from the SAME per-codepoint
`resolved_font_advances`, so layout, paint and Draw IR still measure a run
identically -- only the wire arity differs.

This also removes a silent degradation nobody had named: both
`draw_ir_text_resolved_font` (`src/lib/common/ui/draw_ir.spl:311-315`) and the
protocol validator (`browser_renderer_protocol.spl:2090-2101`) require
`advance_widths.len()` to equal the CODEPOINT count. A byte-expanded array
therefore failed those checks upstream, and every non-ASCII resolved run was
quietly demoted to the flat styled command before Engine2D ever saw it. With
per-codepoint arity those runs now carry their real metrics.

### Evidence (interpreter, `SIMPLE_2D_BACKEND=cpu_simd`)

- `draw_ir_em_dash_text_ink_spec.spl` — 2 examples, 0 failures.
- `paint_layout_advance_parity_spec.spl` — 2 examples, 0 failures.
- `inline_run_advance_and_break_boxes_spec.spl` — 5 examples, 0 failures.
- `font_advance_codepoint_arity_spec.spl` — 9 examples, 0 failures.

### Sabotage, reported honestly

Two producer-side sabotages were run and BOTH left
`draw_ir_em_dash_text_ink_spec` green (2/2): (a) re-emit the byte-expanded array
with no arity prop; (b) keep the per-codepoint array but declare
`font-advance-arity: byte`. (b) also printed no `[e2d-adv]
arity-declared-mismatch` line at all. The reason is not a hole in the gate: that
spec builds its `DrawIrCommand` directly with `draw_ir_text_resolved_font`
(spec lines 40, 62) and never calls the browser-engine producer, so no edit to
`_html_draw_ir_resolved_text_command` can move it either way. It pins the
consumer half — "an em dash does not blank the page" — which is what it was
written for.

The producer half is pinned instead by a REAL page render. With sabotage (b)
applied, `check-chrome-catalog-pixel-diff.shs --simple-only --pages html`
printed, from the Engine2D gate itself:

```
[e2d-adv] arity-declared-mismatch declared=byte advances=71 chars=71
[e2d-adv] text-advance-arity-fallback text_len=73 shaped=false
```

That single pair is the positive proof this follow-up owed, and it says three
things at once: the `font-advance-arity` prop really is on the wire and read by
`_engine2d_draw_ir_text_advances`; the array it describes is per-CODEPOINT
(`advances=71` equals `chars=71`, not the 73 bytes of the same run); and a
declaration that disagrees takes the paint fallback rather than blanking the
page (`mismatch_pct` stayed 17.11). Restoring `codepoint` removes both lines.

Note what this does NOT claim: `html` measures 17.11 both clean and sabotaged,
so no pixel on that page discriminates the two. At origin/main the byte-arity
array was already rejected upstream, so 17.11 is the "resolved run demoted to
flat" figure either way; the improvement is that the codepoint path is now live
and taken, evidenced by the gate's own lines above rather than by a pixel.
