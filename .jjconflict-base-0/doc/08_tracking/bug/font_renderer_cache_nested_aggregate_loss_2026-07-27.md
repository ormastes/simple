# WM font cache: has_ttf=0 on 117/118 resolves — nested array-bearing aggregate loses payload across module-global store/read-back

- **Date:** 2026-07-27
- **Lane:** SimpleOS-WM QEMU (cranelift native), font metric resolution
- **Status:** root-caused (read-only analysis); fix direction described; NOT blocking the now-green SimpleOS-WM cell
- **Family:** cranelift native aggregate-return nil-receiver (`cranelift_native_aggregate_return_nil_receiver_hosted_wm_2026-07-26.md`)

## Symptom
Per `simpleos_wm_pointer_release_font_metrics_hang_2026-07-26.md` rerun52/53:
`has_ttf=0` on 117 of 118 metric resolves; exactly one real font load succeeds;
resolved-metric cache reads `keys=0 values=0`. Nearly all WM text falls back to
the legacy bitmap renderer. The lane is green only because the render now
completes in time, not because the font pipeline is healthy.

## Ruled out: the `has_`-prefix field bug
`has_ttf` / `has_sffi_ttf` are genuine declared methods
(`font_renderer.spl:682,901`), invoked with `()` at every call site
(engine.spl:1333,1530; font_renderer.spl:292,1088,2036). No struct field named
`has_ttf` exists. The known `has_`-prefix bare-field miscompile does NOT apply;
its rename workaround is irrelevant here.

## Root cause (leading hypothesis, strong evidence)
rerun52 breakdown: `74 from_cache=1 has_ttf=0`, `43 from_cache=0 has_ttf=0`,
`1 from_cache=0 has_ttf=1`.

`_browser_default_for_family_cached` (font_renderer.spl:281-297) pushes a whole
`FontRenderer` **by value** into the module-global `[FontRenderer]`
`_browser_default_font_renderers` (:206) **only when `has_sffi_ttf()` was true**
at push time — yet all 74 later index-reads of that same slot report
`has_sffi_ttf()==false`. The cache array itself persists and is hit (rerun52
refuted "cache never persists"); what degrades is the **nested face payload**:
`FontRenderer` embeds `ttf_rasterizer: FontRasterizer?` whose `selected_blob:
[u8]` is exactly what `is_current()` -> `cache_identity_generation()`
(spl_fonts.spl:566-583) needs non-empty for the registered-bytes load path.

This is the aggregate-store/read-back landmine the file's own comments already
document for `self.cache` (font_renderer.spl:712-716, 941-947) — just never
applied to `ttf_rasterizer`. The 43 fresh misses are a second face of it: with
`_registered_selected_fonts_only=true` (font_bootstrap.spl:9) the dlopen
fallback is skipped, so a degraded lookup in the nested `[[u8]]` module global
`_registered_selected_font_blobs` (:208) starves those candidates too.

`keys=0 values=0` is downstream: `_resolved_font_metric_store` only runs when
`resolved.valid`, which requires `has_sffi_ttf()` true — so 117/118 early-return
before ever reaching the store. Confirm after fixing the root.

## Fix direction (describe only)
Stop storing the nested `FontRenderer`/`FontRasterizer` object graph in a
module-global array. Cache flat scalars/text per family (family, resolved path)
and reconstruct a fresh `FontRasterizer` via `try_load_selected_bytes` on each
hit — the same flatten-the-aggregate pattern already used for `FontRenderBatch`
staging. Structurally immune to the store/read-back defect; still avoids VFS
re-parse.

## Verify
Caller-side only (probing inside font_renderer.spl has regressed the lane
before): add an exported `browser_default_font_cache_probe(family) -> (has_entry,
entry_has_ttf)` and compare push-time vs read-time state from
`window_scene_draw_ir.spl`. Fixing the root should raise `has_ttf=1` on repeat
family resolves and make the metric cache populate (`keys>0`), closing the
downstream symptom as a side effect.

## Priority
Follow-up quality item; the SimpleOS-WM matrix cell already PASSES. The proper
fix likely rides the cranelift aggregate-return fix (Codex #20 family) or a
Simple-side flatten workaround; do NOT edit font_renderer.spl while rendering
sessions are active without atomic-write coordination.
