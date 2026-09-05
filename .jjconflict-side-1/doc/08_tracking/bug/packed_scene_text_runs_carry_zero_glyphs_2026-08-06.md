# Packed-scene TEXT runs carried zero glyphs — no showcase target rendered any text

- **Filed:** 2026-08-06
- **Status:** FIXED (producer side) — see "Fix" below
- **Severity:** High — silent; every target painted a text-shaped hole and reported success
- **Component:** `common.ui.widget_draw_ir` (DrawIR v2 producer) → DrawIR v3 text runs
- **Found by:** the GUI showcase migration lane, reported as
  `run present=true count=0 start=4294967295 g0present=false` on all 33 TEXT commands

## Classification: missing feature, not a regression

This was **never wired**, rather than broken by a recent change. No glyph source
existed for ordinary (non-complex-script) text at any point in this pipeline.
The v2→v3 adapter was **not** at fault — it faithfully converted what it was
given, including faithfully converting "no glyphs" into `glyph_count=0`.

## Where the glyphs were lost

`src/lib/nogc_sync_mut/text_layout/font_renderer.spl:2347` sets

```
shaping_required: complex_script != 0
```

and populates `glyph_run` only from the shaping material. So for Latin/ASCII
text, `metrics.valid == true` and `metrics.glyph_run.valid == false`.

`src/lib/common/ui/widget_draw_ir.spl:173-175` (pre-fix) then branched on that
flag: only `shaping_required` text took `draw_ir_text_shaped_font` (which
carries a glyph run); everything else took `draw_ir_text_resolved_font`, which
carries advances and width but **no glyphs at all**.

`src/lib/common/ui/draw_ir_v2_to_v3.spl:331-349` converts faithfully: with
`cmd.glyph_run.valid == false` it emits `glyph_start = DRAW_IR_V3_NO_ID` and
`glyph_count = 0`.

The loss is terminal because **the v3 text-run table has no string field**
(`DrawIrV3TextRunTable`, `draw_ir_v3.spl:117-128`, is glyph columns only). Once
a run reaches v3 with zero glyphs there is nothing for any consumer to fall back
on, so `scene_raster._raster_text_run` (`scene_raster.spl:116`) early-returns.

### Measured, before the fix

Seed binary `bin/simple` → `bin/release/x86_64-unknown-linux-gnu/simple`, md5
`ed53cc5f255e269ca27c4cd83b17aef9`, interpreter (the probe's module drops to the
interpreter via `[jit-fallback] unresolved external symbol 'showcase_build_sized'`):

```
stage0_metrics valid=true shaping_required=false reason=resolved advances=5 glyph_run_valid=false glyph_ids=0
stage1_v2 text_commands=18 with_glyphs=0
stage2_v3 text_runs=18 with_glyphs=0 total_glyphs=0
v3_glyph_table_len=0
```

After the fix, same probe: `stage1_v2 ... with_glyphs=18`,
`stage2_v3 text_runs=18 with_glyphs=18 total_glyphs=120`, `v3_glyph_table_len=120`.

## Why this stayed invisible — the painted counter lies for text

`raster_scene_into` (`scene_raster.spl:147-150`) increments its `painted`
counter for a TEXT command whenever `text_run_id != NO_ID`, **without checking
that any glyph was drawn**. So a scene of pure text renders a blank surface and
still reports a healthy `painted=N`. The GUI lane's `showcase_scene_commands=56;painted=19`
is exactly this shape. Any evidence built on that counter cannot distinguish
"text rendered" from "text silently skipped".

## What this makes vacuous — and what still stands

**Vacuous (do not cite as evidence of text rendering):**

- `showcase_core`'s documented "every input is VISIBLE in the next frame"
  probe-pane mechanism, on **all four** targets (2d / gui / web / wm). The probe
  panes are text; they rendered nothing.
- Any `frame_diff` / framebuffer-checksum comparison whose only expected delta
  was probe-pane *text*. The GUI lane's `showcase_event_frame_diff_total=0`
  across click/toggle/advance is the direct instance.
- `painted=N` counts on text-bearing scenes, per the section above.
- The `ppm_distinct_colors` non-blank checks, **as evidence about text** — they
  legitimately prove the scene is non-blank, but the colours came from rects.

**Still valid (unaffected — these never depended on glyphs):**

- All RECT / EDGE rasterization and the whole-framebuffer occlusion equivalence
  work (`compositor_occlusion_spec`), which compares full redraws of rect chrome.
- Event routing and state transitions: `showcase_apply` was independently
  confirmed to fire (`clicks=0->3`), so the enum-match defect is **not** implicated.
- Scene structural counts (command counts, ids, owner chains, generations) and
  the L0–L9 packed-scene lane evidence, none of which asserted glyph output.
- The 2d host's PPM non-blank checks as evidence that *the pipeline runs*.

## Fix

`src/lib/common/ui/widget_draw_ir.spl` — synthesize a glyph run for text the
shaper does not handle:

- `_charset_glyph_run(x, y, value, advances)` emits charset indices from
  `common.ui.glyph_bitmap_5x7.glyph_index_for_char`, absolute pen positions
  accumulated from `advances`, and a baseline of `y + 7`. Charset indices are
  the id convention this pipeline already uses (`engine2d/glyph.spl`, the
  browser paint primitives, `font_rasterizer.spl`) — no second font mapping is
  invented. It refuses (returns an empty payload) if the advance table and the
  character count disagree, rather than emitting a drifting run.
- `_shift_glyph_run_y` moves a run when `_default_text_centered` re-positions a
  command after building it. Without this the box centres and the text stays
  behind — a bug the fix would otherwise have introduced.

The complex-script path is untouched and still takes precedence.

## Not fixed / still open

- **The shaping path is unreachable in this build.** Probing Arabic text fails
  with `error: semantic: unknown extern function: rt_font_load_bytes`, so
  `shaping_required` text cannot produce glyphs here at all. Complex-script
  rendering is therefore still unproven; only the Latin path is fixed.
- **Glyph size is pinned to the 5x7 bitmap cell**, so `font_size_milli` in the
  v3 run is carried but not honoured by the synthesized geometry. Real
  scalable-font glyph runs need the shaping path above.
- **v2→v3 coordinate convention for shaped runs is unverified.**
  `draw_ir_v2_to_v3.spl:340-341` passes shaping `xs`/`ys` through unchanged while
  the rasterizer treats them as absolute surface coordinates. If the shaping
  material's pen positions are run-relative, shaped text will be mispositioned.
  Untestable here (see the unreachable-extern item).

## Verification

`test/01_unit/lib/common/ui/widget_draw_ir_glyph_run_spec.spl`:
`declared>=4 executed=4 passed=4 failed=0 dropped=0`.

Anti-vacuity is explicit: the examples assert a *positive* glyph count (an empty
tree cannot pass by having no text), assert the shared glyph table length equals
the summed run counts, and pin the defect's signature directly — a zero-glyph
run rasterizes to a **literally blank** surface.

Sabotage-checked: disabling the synthesis turned the file to
`passed=2 failed=2`, with exactly the two pipeline examples failing; the file
was then restored byte-identical to its pre-sabotage copy and re-verified at 4/4.

No regression in the adjacent specs: `draw_ir_v2_to_v3_spec` 13/13,
`widget_draw_ir_theme_spec` 8/8. `bin/simple lint` on both changed files:
exit 0, 0 errors.
