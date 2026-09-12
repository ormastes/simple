# Engine2D stages one text quad per BYTE against a per-CODEPOINT advance array — a single em dash renders the whole page black

- Status: OPEN. Root cause located and reproduced at `origin/main`; the fix is in
  Engine2D / `draw_ir_adv`, which round 5 does not own. Round 5 landed a
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

## Not done here

The producer-side `_html_draw_ir_byte_advances` expansion is still emitting the
byte-arity array. It is now the non-canonical of two accepted conventions;
switching it to per-codepoint (and stating `font-advance-arity: codepoint`) is a
one-file follow-up for the browser-engine lane.
