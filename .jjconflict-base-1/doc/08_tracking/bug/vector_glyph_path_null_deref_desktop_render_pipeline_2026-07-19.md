# Vector glyph path null-deref (font glyph cache) — fixed; residual downstream fault in render pipeline

- **ID:** vector_glyph_path_null_deref_desktop_render_pipeline_2026-07-19
- **Status:** Font glyph path FIXED (verified 0 exceptions from `glyph_with_cache` across
  4 consecutive calls, -kernel and OVMF). Boot still shows exactly 1 residual exception
  frame, now firing AFTER `draw_text_configured-entry`, matching the signature already
  tracked in `engine2d_cpu_offscreen_render_commands_first_frame_fault_2026-07-17.md`
  (fault immediately follows `[heap] alloc sz=0x800020` bursts) — likely the same
  downstream subsystem, not font code. Not yet root-caused; out of scope for this session
  (edit surface was `font_renderer.spl` + `font_rasterizer.spl` + `engine.spl` font
  plumbing only).
- **Severity:** was high (boot-time null deref on every degenerate/0x0 glyph); now
  reduced to a single, non-font-path exception per boot.
- **Lane:** SimpleOS x86_64 desktop (`gui_entry_desktop.spl`), -kernel and OVMF pflash.

## Original symptom (fixed)

`FontRenderer.glyph_with_cache` faulted (cr2=0x0 null deref) handling a degenerate
(w=0/h=0) glyph returned by the SFFI spl_fonts rasterizer. Root cause matched the
compiler-level landmine documented in
`native_tuple_spill_clobber_across_call_2026-07-19.md`: a struct value
(`_sffi_glyph_to_cached`'s `GlyphBitmap`/`CachedGlyph` return) crossing a module
boundary, re-read after an intervening call (a diagnostic `print()`, or
`cache.insert()`), resolves to unrelated/unmapped heap memory once enough
allocations have happened between the two reads — heap-layout dependent, not
deterministic per call.

## Fix (landed this session)

- `src/lib/nogc_sync_mut/text_layout/font_renderer.spl`
  (`FontRenderer.glyph_with_cache`): read every field of the SFFI-returned glyph
  exactly once, immediately, into locals (no further call in between); rebuild
  `glyph` as a fresh same-module `CachedGlyph` struct literal so nothing downstream
  re-reads the cross-module value. Degenerate glyphs (`w<=0 or h<=0`) get a
  fresh, empty-`pixels` "advance-only" cache entry — no pixel-buffer deref, no
  atlas insert (atlas insert was already width/height-guarded).
- `src/lib/nogc_sync_mut/text_layout/font_rasterizer.spl`
  (`_sffi_glyph_to_cached`): read scalar metrics first in one straight-line pass;
  for a degenerate glyph, return immediately WITHOUT ever touching
  `gb.gbm_pixels` (the array field). No `print()`/other call sits between the
  scalar reads and the return — an earlier attempt added a diagnostic probe
  there and the crash immediately relocated to right after that probe, which is
  itself evidence for the "intervening call" mechanism above.

## Verification

Boot serial (`build/os/_wkheap/serial-diag.log` and `serial-ovmf.log`, both from
the same final `desktop.elf`) shows, for codepoint 0 / font_size 12 (a
degenerate glyph — the actual codepoint value is unreliable due to the
separately-tracked `native_char_code_at_tag_shift_2026-07-19.md` bug, not chased
here):

```
gwc-entry cache_entries=0                # call 1: cold, rasterizes
gwc-pre-rasterize / gwc-post-rasterize / gwc-post-to_cached / gwc-pre-insert   # completes cleanly, inserts
gwc-entry cache_entries=1                # call 2: cache HIT, no rasterize, no fault
gwc-entry cache_entries=1                # call 3: cache HIT
gwc-entry cache_entries=1                # call 4: cache HIT
draw_text_configured-entry plan_len=6
[heap] alloc sz=0x800020 (x2)
[fault] *** EXCEPTION FRAME *** cr2=0x0   # residual — NOT in glyph_with_cache
```

Zero exceptions trace to `glyph_with_cache`/`_sffi_glyph_to_cached` across all 4
calls in either boot mode. The one remaining exception fires after font-glyph
processing has already completed for this text run, immediately following two
`0x800020` (~8MB) heap allocations — the same adjacency the 2026-07-17 doc flags
for the offscreen/render-commands compositor path. Screen coverage stayed
99.83% nonblack in every boot (before and after this fix); the clock-region
sample (right 56px x bottom 48px) shows only 2 flat colors both before and
after, so no anti-aliased glyph-shaped pixels are confirmed yet either way —
GLYPHS: NOT YET CONFIRMED VISIBLE, blocked on the residual fault above rather
than on font code.

## Repro

`scratchpad/glyphfix4_build.sh` (cache `build/os/_cache_glyphfix4/cache`), deploy
to `build/os/_wkheap/desktop.elf`, boot via `scratchpad/boot_diag_wkheap.sh`
(-kernel) or `scratchpad/boot_ovmf_wkheap.sh` (OVMF pflash, board-runnable
proxy) — both reproduce identically (1 exception, same probe sequence).

## Next step

Root-cause the residual `0x800020`-adjacent fault per the 2026-07-17 doc's
"Fix direction," or extend probing there (raise/dedicate a probe budget — this
session's shared 8-print `_vec_glyph_probe_count` cap was exhausted by the 4
legitimate `gwc-entry` cache-hit prints before reaching the render-commands
call site, so the exact faulting call could not be pinpointed this cycle).
