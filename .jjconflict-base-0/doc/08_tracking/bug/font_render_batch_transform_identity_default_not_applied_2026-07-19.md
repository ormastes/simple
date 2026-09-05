# BUG: `FontRenderBatch.transform_identity` default field value not applied — reads as empty string, blocking all glyph compositing

## Status
Open (2026-07-19, GLYPH-FIX-8 campaign). Root-cause LOCALIZED, not fixed
(out of this session's edit-surface scope — see below).

## Summary
`class FontRenderBatch` (`src/lib/nogc_sync_mut/text_layout/font_types.spl:220`)
declares a default field value:

```
transform_identity: text = "uniform-scale;translate-late"
```

Every `FontRenderBatch(...)` constructor call site in
`src/lib/nogc_sync_mut/text_layout/font_renderer.spl` (there are ~15, all
in `_prepare_text_active` and sibling `prepare_*` methods) omits
`transform_identity:` explicitly, relying on this class default. At
runtime on the freestanding x86_64 SimpleOS target, the field reads back as
an **empty string**, not the declared default. This makes
`FontRenderBatch.material_supported()` (and the duplicated inline check in
`Engine2D._draw_font_batch_plan`,
`src/lib/gc_async_mut/gpu/engine2d/engine.spl:972-974`) evaluate to
**false** even when `batch.valid=true` and the program version matches, so
`_draw_font_batch_plan` returns `false` immediately (line 1003-1004) and
**no glyph is ever blitted to the framebuffer**, regardless of whether the
upstream quads are correct.

This is the blocker that remains after
`doc/08_tracking/bug/for_loop_over_text_char_code_at_zero_len_crash_2026-07-19.md`'s
indexed-loop workaround was applied in GLYPH-FIX-8: the for-loop corruption
bug is fully worked around (codepoints, rasterization, and atlas quad
coverage are all now correct — see that doc's Status update), but glyph
text still does not appear on the SimpleOS desktop render because of this
separate, independent defect.

## Evidence

Temporary diagnostic print added directly at the `material_ok` computation
in `Engine2D._draw_font_batch_plan` (reverted before final deploy; not
part of the shipped diff):

```
print("[glyphfix8-diag] pv={batch.program_version} pv_ok={font_atlas_composite_program_version_valid(batch.program_version)} ti={batch.transform_identity} ti_ok={batch.transform_identity == "uniform-scale;translate-late"} valid={batch.valid}")
```

Serial output from a `-kernel` diag boot (7 samples, all identical):

```
[glyphfix8-diag] pv=1 pv_ok=1 ti= ti_ok=0 valid=1
```

- `pv=1 pv_ok=1` — `program_version` is correct (explicitly set at every
  construction site to `FONT_ATLAS_COMPOSITE_PROGRAM_VERSION`); not the bug.
- `valid=1` — the `valid` bool field reads correctly; not the bug.
- `ti=` — **`transform_identity` prints as an empty string**, not
  `"uniform-scale;translate-late"`. This is the sole failing sub-condition
  of `material_ok = batch.valid and font_atlas_composite_program_version_valid(batch.program_version) and batch.transform_identity == "uniform-scale;translate-late"`.

Also confirmed via the pre-existing `[vec-text-probe] consumer ...` probe
(`_VEC_TEXT_PROBE`, `engine.spl:975-1002`): `valid=1 material_supported=0
n_quads=1..13 ... first_cov_nz=8..38 color_a=255` — i.e. quads with real,
nonzero glyph coverage reach the consumer and are still rejected by the
`material_ok` gate.

## Impact

Full stop for glyph text rendering on the SimpleOS freestanding x86_64
target: `_draw_font_batch_plan` is the single choke point every
`draw_text`/`draw_text_configured`/`draw_glyph_run` call goes through, and
it bails before attempting any backend (cuda/metal/opencl/vulkan/rocm/cpu)
when `material_ok` is false. Confirmed both `-kernel` and OVMF
(real-firmware) desktop boots: `desktop-ready` + `first-frame-rendered` +
0 exception frames + 99.83% nonblack framebuffer, but 0 pixels near the
text color and a flat 2-color taskbar-clock region in both.

## Likely root cause (not yet confirmed by source inspection of codegen)

A class-field default-value (`field: T = <expr>` syntax) is not being
applied when a constructor call omits that field, specifically for a
`text`-typed default on this freestanding/native-codegen target. Plausible
sibling candidates worth checking once someone picks this up:
- Do `render_config_identity`, `execution_target`, and `execution_policy`
  (the other three defaulted fields on the same class, declared
  immediately around `transform_identity`) exhibit the same symptom, or is
  it specific to `text`-typed defaults / this particular field's position
  in the class? Not tested in this session (would require another
  diagnostic print + rebuild cycle, out of this session's remaining
  budget).
- Whether this reproduces in the hosted interpreter (not just the
  freestanding native-build target) — not tested in this session.

## Why not fixed in this session

Out of GLYPH-FIX-8's declared edit surface (`font_renderer.spl` +
`spl_fonts.spl`, indexed-loop recipe only). The actual bug lives in class
default-field-value codegen/interpreter semantics (shared compiler
infrastructure, not `font_renderer.spl`/`spl_fonts.spl` content), so fixing
it here would be scope creep beyond the coordinator-approved mission. Two
independently-viable, in-scope-for-a-future-session fix directions:
1. Fix the underlying default-field-value application bug (wherever it
   lives in `src/compiler_rust` or `src/compiler` construction lowering) —
   the correct, general fix.
2. Narrow workaround: explicitly pass `transform_identity:
   "uniform-scale;translate-late"` at every `FontRenderBatch(...)`
   construction site in `font_renderer.spl` that currently omits it. This
   is the same "don't rely on the buggy path, name it explicitly" pattern
   as the for-loop workaround, and would very likely unblock the render
   without touching shared compiler code — but is out of THIS session's
   edit surface and needs the next coordinator go-ahead.

## Confirmation test (diagnostic only, NOT deployed)

To validate the diagnosis without expanding GLYPH-FIX-8's authorized edit
surface, `_font_render_batch_with_config`
(`font_renderer.spl:266-276`, itself part of the same file as the
authorized indexed-loop fix) was temporarily changed:

```
- render_config_identity: font_render_config_identity(config), transform_identity: batch.transform_identity,
+ render_config_identity: font_render_config_identity(config), transform_identity: "uniform-scale;translate-late",
```

Rebuilt to a throwaway diagnostic output (`build/os/_cache_glyphfix8diag/`,
never copied to the deployed `build/os/_wkheap/desktop.elf`), booted
`-kernel`:

```
COVERAGE 3840x2160 nonblack=8280330/8294400 (99.83%) colors=19   (was 14)
textpx~(29,29,31)tol8=70 bbox=(1,1)-(6,15)                        (was 0, bbox=none)
clock_region: still 2 colors, 0 text pixels                       (unchanged)
```

**This confirms the diagnosis**: hardcoding `transform_identity` unblocks
`material_ok` and a real glyph DOES appear on screen. Verified rigorously
by a full pixel-level diff of the two screenshots (same seed, same
boot script, ONLY the `transform_identity` line differs between the two
builds — `shot-diag.ppm` = deployed indexed-loop-only build,
`shot-diagprobe.ppm` = + transform_identity hardcode, both probes off):

```
total_pixels=8294400 diff_pixels=73 bbox=(1,1)-(6,15)
num_distinct_64x64_cells_touched=1   (cell (0,0), i.e. screen origin only)
```

ASCII art of the (0,0)-(9,17) region where every `#` is a changed pixel:
```
..........
.####.....
.######...
.######...
.######...
.######...
.######...
..#####...
..#####...
..#####...
..###.#...
..###.#...
..#####...
..#####...
...###....
...###....
..........
..........
```
A genuine filled/rounded glyph-sized blob (~6x14px), and the color
transition at those pixels is `(245,245,247) -> (29,29,31)` — i.e. FROM the
light background color TO the campaign's established anti-aliased text
color (`~0x1d1d1f`, the exact color the pixel-analysis tooling in this
campaign filters for). This is unambiguously a real rendered glyph, not
noise: fix direction #2 above is a working (partial) unblock, not just a
hypothesis.

**It does NOT close the goal.** The diff proves ALL of the frame's change
is this one ~73px glyph at the screen origin — not the taskbar clock
(bottom-right), and not any window title or other taskbar label (colors
14→19 in the earlier coarse check was fully explained by this single glyph,
not broad text rendering as first suspected from that weaker signal; the
full pixel diff is definitive). Of the ~7 live text draw calls this
campaign's earlier probes showed producing valid, nonzero-coverage quads
(`n_quads=1,10,8,13,13,5,5` at `[vec-atlas-probe] producer`,
`for_loop_over_text_char_code_at_zero_len_crash_2026-07-19.md`), only ONE
actually reaches the screen even with `transform_identity` fixed. This
points to a THIRD, still-uninvestigated factor blocking most text draws
(taskbar clock included) — separate from both the for-loop bug and this
`transform_identity` default-field bug. Not investigated further in
GLYPH-FIX-8 (edit-surface + iteration-budget exhausted); candidates for a
follow-up session, roughly in order of how well they fit "only the first of
several sequential draws survives":
- The shared font atlas's generation/identity-mismatch reset path
  (`_prepare_text_active`, `font_renderer.spl` ~line 1160-1166: `if
  end_generation != face_generation or end_identity != font_identity: ...
  return invalid batch`) — if each successive text draw mutates atlas state
  in a way that invalidates the NEXT draw's snapshot, only the first draw
  in sequence would ever produce a `valid: true` batch. This shape matches
  the evidence (first draw survives, rest don't) better than a per-call
  `dst_x`/`dst_y`/blit issue would.
- The `dst_x`/`dst_y` nil guard in `_draw_font_batch_cpu_suffix`
  (`engine.spl:946-950` — blit is skipped entirely if either is `nil`), or
  `draw_image_blend` itself — plausible but doesn't obviously explain why
  specifically the FIRST draw succeeds and later ones don't.
- The taskbar-clock call site being routed through a different
  `config`/execution plan than whichever call produced the (1,1)-(6,15)
  glyph.

This temporary edit was reverted before the final GLYPH-FIX-8 deploy;
`font_renderer.spl`'s only shipped change in this session is the indexed-loop
recipe from `for_loop_over_text_char_code_at_zero_len_crash_2026-07-19.md`.

## Repro

Build `build/os/_wkheap/desktop.elf` (current source, GLYPH-FIX-8's
indexed-loop fix applied), boot via `scratchpad/boot_diag_wkheap.sh` or
`scratchpad/boot_ovmf_wkheap.sh`, screendump, and check the taskbar-clock
region (rightmost 56 x bottom 48 px) — 2 flat colors, 0 text-color pixels.
Re-add the `[glyphfix8-diag]` print above (temporarily) at
`engine.spl:974` under the existing `_VEC_TEXT_PROBE` gate to reproduce the
`ti=` empty-string evidence directly.

## Related
- `doc/08_tracking/bug/for_loop_over_text_char_code_at_zero_len_crash_2026-07-19.md`
  (workaround applied in the same GLYPH-FIX-8 session; this bug is the
  next blocker after that one)
- `src/lib/nogc_sync_mut/text_layout/font_types.spl:208-238` (`FontRenderBatch`
  class + `material_supported()`)
- `src/lib/gc_async_mut/gpu/engine2d/engine.spl:918-1099` (`_draw_font_batch`,
  `_draw_font_batch_cpu_suffix`, `_draw_font_batch_plan` — the compositing
  choke point)
