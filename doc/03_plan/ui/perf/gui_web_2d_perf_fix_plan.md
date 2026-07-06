<!-- opus perf-triage 2026-07-06 -->
# GUI / Web / 2D Rendering Perf-Fix Plan

**Status:** READY-TO-DISPATCH (2026-07-06) · **Scope:** ranked, measured, disjoint-file fix items
across the three render lanes (GUI present loop, web HTML render, engine2d software rasterizer).

**Sources:** three read-only measurement passes —
`scratchpad/perf_gui.md`, `scratchpad/perf_web.md`, `scratchpad/perf_2d.md` (all numbers below are
direct measurements from those passes, reproduced commands live in each source file).

**Arch constraints honored:**
- `doc/04_architecture/ui/rendering/backend_isolation_architecture.md` — apps call facades only; no
  new per-call hop on the four preserved fast paths (Metal no-mirror, batched Metal FFI, NEON/SSE2
  row kernels, `WebRenderPixelArtifactCache`).
- `doc/05_design/ui/rendering/draw_ir_multibackend_design.md` §D2 — `SharedRaster`/`backend_emu` is
  the single parity oracle; **any pixel-changing op edit must flip its assertion through the
  committed harness** `test/02_integration/rendering/engine2d_shared_raster_parity_spec.spl`. Output-
  preserving edits keep the harness assertion `== 0`.

---

## Explicitly EXCLUDED (do NOT touch — in-flight or seed-blocked)

| Excluded item | Why | Evidence checked |
|---|---|---|
| `src/app/ui.browser/app.spl`, `main.spl`, and the `gui_renderer`/`spl_winit` stack | **Task #25 in-flight** | `app.spl` mtime `Jul 6 14:33`, `main.spl` `Jul 6 14:32` — actively edited today |
| `#15` WM pixel-cache items (`WebRenderPixelArtifactCache` wiring) | **Already landed** — nothing to do | Wired at `src/app/ui.browser/backend.spl:337` (`web_render_pixel_cache`) and `src/os/compositor/host_compositor_entry.spl:247` (`content_caches: Dict<i64, WebRenderPixelArtifactCache>`). Any content-hash frame cache for identical HTML is already served here. |
| **Web Rank 1** — Metal `draw_image`/`read_pixels` one-call path (`rt_write_u32s_to_raw` / `rt_u32s_from_raw`) | **Rust seed/runtime extern change** | Finder confirmed `SIMPLE_ONE_CALL_READBACK=1` crashes today: `unknown extern function: rt_write_u32s_to_raw`; the fix is *wiring the missing runtime extern*, which is off-limits per "no Rust seed changes". Filed to the runtime-extern owner separately. |
| **2D Rank 2/3** — bulk `clear`/`read_pixels` memset + real `cpu_simd` | Both blocked on the **mutable-array-extern bridge** (`doc/08_tracking/bug/cpu_simd_mutable_array_extern_wiring_2026-05-31.md`), a runtime/seed change | Finder confirmed no proven interpreter mutable-array extern; both fixes route through `rt_array_fill_u32`/`rt_engine2d_simd_*`. |
| **GUI Rank 5b** — winit `[u32]` FFI signature + `get_pixels` per-element match | Rust extern (`interpreter_extern/winit_sffi/mod.rs`) | Seed change. Only the *Simple-side* dirty-gate half (GUI-5a) is in scope below. |
| **GUI Rank 4** — lazy backend load / GPU import lint noise | Compiler-diagnostic / backend-isolation redesign, Medium-High risk | Out of a quick-fix pass; not a lane-local change. |
| **Web Rank 3** — parse-artifact content-hash cache | Superseded/occupied by the landed `#15` pixel cache (identical-content frames already short-circuit at `BrowserBackend.render_frame`/`host_compositor_entry`); the remaining "slightly-different-frame parse reuse" case is speculative | See `#15` row above. Re-evaluate in a future wave if a non-identical-but-reparseable workload is demonstrated. |

---

## Fix agents (≤3 items each, DISJOINT file sets)

### AGENT `fix-gui` — GUI present loop (one file)

**Owned files (exclusive):** `examples/06_io/ui/widget_showcase_gui.spl`

All three items are output-preserving and live entirely in this example; they do not touch any
facade/backend/`rt_*` surface (they change *when* and *how often* the same `Engine2D` calls run).

| # | Symptom + measured evidence | Hot spot | Fix | Guard | Expected win | Risk |
|---|---|---|---|---|---|---|
| GUI-1 | **Every redraw rebuilds+destroys a whole `Engine2D` + re-interprets all 24 widget draws.** `build_frame_state()` alone = **7.12s** for one 520×660 frame (module-load excluded via per-line timestamps); ~20.5µs/px, 21.5s user-CPU at 1024². The 500ms tick re-triggers it unconditionally — 14x the tick interval. | `widget_showcase_gui.spl:440-449` (`build_frame_state` create→draw→`shutdown` every call) + `:887-893` (present loop calls it on dirty) | Create ONE `Engine2D` before the `while running` loop; on dirty do `clear()` + redraw into the same engine instead of `create_with_backend`/`shutdown` per frame. Same API, same call sequence, moved out of the loop. | Dump frame pixels before/after → byte-identical; add a frame-time regression assertion (`build_frame_state` < 1s at 520×660). Reuse `scripts/check/check-engine2d-nomirror-fast-render-evidence.shs` shape for the evidence harness. | Removes full engine churn paid ≥2×/sec; interactive framerate becomes draw-call-bound, not backend-churn-bound. Largest single win in the plan. | Low |
| GUI-2 | **Startup builds a throwaway 64×64 `Engine2D` just to log one diagnostic line** (contributes to the 269MB `IOAccelerator` footprint on the "software" app). | `widget_showcase_gui.spl:429-437` (`emit_renderer_log`) | For any key ≠ `"vulkan"` the backend name is deterministic from the requested key string — drop the probe engine construct/shutdown; format the log from the requested-key string. | Assert the emitted `showcase_renderer_backend=…` log line is byte-identical to today for each key; footprint spot-check (baseline vs after). | Removes one full engine construct+init+shutdown cycle at startup. | Low |
| GUI-5a | **Native winit loop presents unconditionally every ~30ms** even when nothing changed (`winit_present_rgba` called before the `if dirty:` rebuild). | `widget_showcase_gui.spl:875` (unconditional present) vs `:888` (dirty-gated rebuild) | Move the `winit_present_rgba` call inside the existing `if dirty:` block. (Simple-side only; the `[u32]` FFI-signature half is excluded — seed.) | Idle-CPU cross-check (`ps -o %cpu`) on an idle instance drops toward the ~1.3% the correctly-gated WM-client loop already measures; visual output unchanged when dirty. | Idle-loop present/FFI traffic → near zero when untouched. | Low |

---

### AGENT `fix-web` — web CSS cascade bucket build (one file)

**Owned files (exclusive):** `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`

| # | Symptom + measured evidence | Hot spot | Fix | Guard | Expected win | Risk |
|---|---|---|---|---|---|---|
| WEB-2 | **`build_rule_buckets` selector-key dedup is an O(rules × unique_keys) linear scan — superlinear (~n^1.6) in practice.** `compute_styles_ms` on distinct-class CSS at 320×240: 261 (0 extra rules) → 1,024 (700) → 3,715 (1500) → **11,505 (3000)**; doubling rules 1500→3000 triples cost (3.1×) while `extract_css` stays linear. This is the un-fixed "Remaining debt" in `doc/08_tracking/bug/browser_engine_css_size_quadratic_pixel_render_2026-07-04.md`. | `simple_web_html_layout_renderer.spl:4645-4651` (`text_key_index_count`, linear scan over `class_keys_raw[0..count]`), called per-rule at `:4834` (id) / `:4845` (class) / `:4856` (tag) inside `build_rule_buckets:4802` | Replace the 3 linear-scan dedup loops with a `dict<text,i32>` insert-or-get; preserve first-seen order via the existing `entry_*` arrays so bucket assignment/order is unchanged. O(1) amortized per rule. | Must stay green: `test/02_integration/rendering/simple_web_css_cascade_spec.spl` and `test/01_unit/app/ui/browser_backend_pixel_paths_spec.spl` (same specs that validated the sibling `apply_decls` fix — they lock cascade order). Re-run the finder's distinct-class scaling probe to confirm `compute_styles_ms` goes linear. | Several seconds off `compute_styles` at real 1990-rule themes (CARD16 blocker); pairs with the excluded Metal one-call fix to reach the sub-2s render target. | Low — internal data-structure swap behind a pure-fn boundary; pixel output unchanged. |

*(One item; web Rank 1/3/4 are excluded above. Adding a second item here would collide with either the
seed-blocked Metal path or the `#15`-occupied cache territory, so `fix-web` stays single-item.)*

---

### AGENT `fix-2d` — engine2d shared reference ops (two isolated files)

**Owned files (exclusive):** `src/lib/gc_async_mut/gpu/engine2d/backend_emu_adv.spl`,
`src/lib/common/ui/glyph_bitmap_5x7.spl`

> **Deliberately avoids `backend_software.spl` / `backend_emu.spl` / the parity spec** — those are the
> files the D2 op-consolidation task edited today (`draw_ir_multibackend_design.md` §"D2 executed
> 2026-07-06"). Keeping `fix-2d` off them prevents a concurrent-edit conflict. Both items below are
> output-preserving, so the parity harness assertion stays `== 0` (agent re-runs it read-only to
> confirm, but does not edit it).

| # | Symptom + measured evidence | Hot spot | Fix | Guard | Expected win | Risk |
|---|---|---|---|---|---|---|
| 2D-1 | **`draw_blur_rect`/`draw_shadow_rect` = 70.6s for one 160×90 r=6 blur.** Two stacked costs: (a) the O((2r+1)²) tap loop calls 4 free functions (`color_r/g/b/a`) **per tap** — ~3.03M taps × 4 ≈ 12M extra interpreted dispatches for this one call; (b) full-canvas `read_pixels()` floor (~0.86s, ~1% of total). | `backend_emu_adv.spl:41-76` (`emu_draw_blur_rect`): tap loop `:57-71` with `color_r/g/b/a` calls; `read_pixels()` at `:44` | **In-scope (output-preserving, this file only):** inline the `color_r/g/b/a` shift/mask math directly in the `kx`/`ky` loop body (drop 4 fn calls per tap). Removes ~12M interpreted dispatches per call. | Parity harness blur/shadow rows stay `== 0` (`engine2d_shared_raster_parity_spec.spl`, run read-only); add a perf assertion (single blur call under a wall-clock ceiling). | ~2-3× on any `blur_r>0` call, output byte-identical. | Low |
| 2D-5 | **`draw_text` ~547µs/char** for <150 actual pixel writes (30-char string = 16,413.8µs, 320×240, scale=1) — per-char allocation, not pixel-bound. | `glyph_bitmap_5x7.spl:97-107` (`glyph_rows_for_char` allocates a fresh 7-elem `[i32]` literal + 7 `glyph_row_bits()` dispatches **per glyph per call** for static bitmap data) | Precompute/cache the 7-row bitmap per charset glyph once (e.g. read the existing packed `FONT_ROWS_PACKED: [i64]` via bit-shifts in the hot path, or a one-time `[[i32]]` table); keep `glyph_rows_for_char` as a compat wrapper. | Parity harness `draw_text` row stays `== 0`; text-rendering output unchanged in both the engine2d and browser paint paths (both consume this table). Perf assertion on the 30-char benchmark. | Low-single-digit-× on text-heavy frames; benefits browser paint too (shared table). | Low — output-preserving, shared module. |

*(`fix-2d` is capped at 2 items to keep it clear of the D2-hot files; the higher-multiplier separable
blur and the gradient one-pass override are deferred below because they are pixel-changing and/or land
on the D2-hot `backend_emu.spl`/`backend_software.spl`.)*

---

## Disjointness matrix (verify before dispatch)

| Agent | Files touched |
|---|---|
| `fix-gui` | `examples/06_io/ui/widget_showcase_gui.spl` |
| `fix-web` | `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl` |
| `fix-2d` | `src/lib/gc_async_mut/gpu/engine2d/backend_emu_adv.spl`, `src/lib/common/ui/glyph_bitmap_5x7.spl` |

No file appears in two rows. None overlap the excluded task-#25 / `#15` / D2-hot files.

---

## Next wave (deferred, with the gate that must clear first)

| Item | Source | Gate before it can be picked up |
|---|---|---|
| **Separable box blur** (true 2-pass, ~6× more on top of 2D-1) | 2D Rank 1 (3) | Pixel-changing (integer-division rounding differs) → must update the D2 canonical reference + flip the parity harness assertion; land only after the D2 consolidation task settles on `backend_emu.spl`/parity spec. |
| **Region readback for blur** (`read_pixels_region(x,y,w,h)`) — removes the ~0.86s full-canvas floor | 2D Rank 1 (1) | Adds a trait method → touches `backend.spl` + `backend_software.spl` (D2-hot). Sequence after D2. |
| **`draw_gradient_rect` one-pass** (6.16× per-px vs plain fill) | 2D Rank 4 | Lands on `backend_emu.spl` (D2-hot) and/or reverses the just-landed sw→emu delegation; needs a D2-aligned decision (shared one-pass vs documented sw override, mirroring the `draw_line` exception). |
| **`clear`/`read_pixels` bulk memset** (50-200× at HD) + real `cpu_simd` backend | 2D Rank 2/3 | Blocked on the mutable-array-extern bridge (runtime/seed). Tracked in `cpu_simd_mutable_array_extern_wiring_2026-05-31.md`. |
| **Metal one-call upload/readback** (2.3-4.2×, grows with viewport) | Web Rank 1 | Blocked on wiring `rt_write_u32s_to_raw`/`rt_u32s_from_raw` runtime externs (seed), then verify bit-exact vs per-pixel path before flipping `SIMPLE_ONE_CALL_READBACK` default-on. |
| **`compositor_engine2d.present_rect` honoring its rect args** + dirty-tile readback | GUI Rank 3 | `backend_software.spl` (D2-hot) + `compositor_engine2d.spl`; sequence after D2, run parity harness after. |
| **Winit `[u32]` FFI signature** (halves marshalled bytes) | GUI Rank 5b | Rust extern change (seed). |
| **Web parse-artifact cache** re-evaluation | Web Rank 3 | Only if a non-identical-but-reparseable workload is demonstrated (identical-content already covered by the landed `#15` pixel cache). |

---

## Dispatch summary (for the orchestration script)

```
fix-gui : GUI-1, GUI-2, GUI-5a   -> examples/06_io/ui/widget_showcase_gui.spl
fix-web : WEB-2                   -> src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl
fix-2d  : 2D-1, 2D-5             -> src/lib/gc_async_mut/gpu/engine2d/backend_emu_adv.spl,
                                     src/lib/common/ui/glyph_bitmap_5x7.spl
```

Each agent: make the edit, run its named guard spec(s), confirm output-preserving (pixel-identical),
attach the before/after perf number, commit on `main` (no branches). All three run in parallel — file
sets are disjoint.
