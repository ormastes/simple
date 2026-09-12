# Engine2D stages one text quad per BYTE against a per-CODEPOINT advance array — a single em dash renders the whole page black

- Status: OPEN. Root cause located and reproduced at `origin/main`; the fix is in
  Engine2D / `draw_ir_adv`, which round 5 does not own. Round 5 landed a
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
