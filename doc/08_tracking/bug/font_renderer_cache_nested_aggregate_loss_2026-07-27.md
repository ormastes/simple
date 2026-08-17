# WM font cache: has_ttf=0 on 117/118 resolves — nested array-bearing aggregate loses payload across module-global store/read-back

- **Date:** 2026-07-27
- **Lane:** SimpleOS-WM QEMU (cranelift native), font metric resolution
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
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

## Resolution (2026-07-30)

Applied the flatten workaround described above. `_browser_default_font_renderers:
[FontRenderer]` (a module-global array storing the whole nested aggregate) is
gone; the loaded-default-font cache is now two flat parallel `[text]` arrays,
`_browser_default_font_families` (cache key) and `_browser_default_font_paths`
(resolved font path). `font_renderer.spl:258-433`:

- `_browser_default_font_load_with_path(family)` — new module fn, factored out
  of `FontRenderer.browser_default_for_family`'s body (which now just delegates
  to it) — resolves a family to `(FontRenderer, font_path, ok)`.
- `_browser_default_font_rebuild_from_path(font_path)` — new module fn used on
  every cache HIT. It reconstructs a fresh `FontRenderer` from the
  already-in-memory registered blob via `try_load_selected_bytes(path, blob)`
  (falling back to `try_load_runtime_ttf(path)` only when registered-bytes-only
  mode is off), so a hit never re-reads the VFS.
- `_browser_default_for_family_cached` stores/reads only the resolved path on
  a hit/miss; `font_renderer_use_registered_selected_bytes_only()`'s reset no
  longer calls `clear_ttf()` in a loop (nothing cached to clear — it just drops
  the two flat arrays).

Public signatures are unchanged: `FontRenderer.browser_default_for_family`,
`font_renderer_use_registered_selected_bytes_only`,
`font_renderer_register_selected_bytes`, `resolve_font_metrics(_with_language)`
all keep their existing shapes.

Landed on `main` as `8bcb6d29fa` (superseded on origin by an equivalent
independent landing of the same flatten shape — content-identical past the
`browser_default_for_family` delegation, confirmed by diff against
`origin/main:src/lib/nogc_sync_mut/text_layout/font_renderer.spl`). Do not
re-apply; the fix is live on `main`.

**Verification is honest but incomplete.** The macOS hosted interpreter lane
(`bin/simple test`) is NOT the lane this bug was measured on — the bug doc's
own evidence (`has_ttf=0` on 74/74 hits) is from the cranelift-native
SimpleOS-WM QEMU lane, which this agent was explicitly told not to touch. On
the hosted interpreter:
- `test/01_unit/lib/engine/font_ffi_spec.spl` — 14/14 PASS (324ms).
- `test/01_unit/lib/common/text_layout/font_renderer_spec.spl` (768 lines, real
  17MB-class TTF parses across ~40 `it` blocks) — times out under the test
  runner's resource-limit guard even at `--timeout 300`, both before and after
  this change; this is a pre-existing interpreter-mode perf characteristic of
  the file (see its own header comment on the dominant real-font-parse cost
  under the interpreter), not a regression introduced here.
- A standalone probe spec (`_font_renderer_reset_registered_selected_bytes_for_test`
  + `font_renderer_register_selected_bytes` for the real "Noto Sans Arabic"
  asset + `font_renderer_use_registered_selected_bytes_only()`, then repeat
  `resolve_font_metrics_with_language("sans-serif", <distinct content>, 32,
  "ar")` calls to force repeat family-cache hits through the flattened path)
  ALSO timed out under the interpreter at even 2 iterations / 500s — real TTF
  shaping cost per call under the tree-walk interpreter is apparently on the
  order of minutes on this machine, independent of this fix. Could not produce
  the "has_ttf succeeds on N>1 of M cache hits" number this session asked for
  as the strongest evidence; state that plainly rather than claim it.
- No cranelift-native / QEMU run was attempted (out of scope per task
  instructions — SimpleOS-WM QEMU work is owned by a dedicated session).

**The underlying compiler defect is still latent.** This is a call-site
workaround only — the cranelift native aggregate-return/nested-array-field
store-read-back defect it works around (family:
`cranelift_native_aggregate_return_nil_receiver_hosted_wm_2026-07-26.md`) is
unfixed. Any future code that stores a class containing a nested `Option`-of-
array-bearing-class field into a module-global array on that lane will hit the
same landmine. No new bug filing needed — it is already tracked under that
family doc; this entry cross-links it.
