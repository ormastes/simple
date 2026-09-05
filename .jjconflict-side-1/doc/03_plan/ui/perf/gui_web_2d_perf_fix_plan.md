<!-- opus perf-triage 2026-07-06 · wave-1 landed 2026-07-07 -->
# GUI / Web / 2D Rendering Perf-Fix Plan

**Status:** WAVE-1 LANDED (2026-07-07) · **Scope:** ranked, measured, disjoint-file fix items
across the three render lanes (GUI present loop, web HTML render, engine2d software rasterizer).

## Wave-1 status (LANDED / REJECTED) — 2026-07-07

Verified against git + bug records. The "Fix agents" section below is the wave-1 dispatch
record (historical); the "Next wave" section is now the live backlog.

| Item | Outcome | Commit / evidence | Verified number |
|---|---|---|---|
| **WEB-2** `build_rule_buckets` dedup (linear scan → dict insert-or-get) | **LANDED** | `b65e52a9` — `perf(web): build_rule_buckets dedup O(rules×keys) linear scan → dict insert-or-get`; +18/-6 on `simple_web_html_layout_renderer.spl` | `compute_styles_ms` at 3000 distinct-class rules **9328 → 5899 ms (~1.6x)** (`doc/08_tracking/bug/web_compute_styles_residual_quadratic_2026-07-06.md`). The dedup contributor is gone; the pipeline is **still superlinear** — see next-wave item N1. |
| **2D-1** inline `color_r/g/b/a` in `emu_draw_blur_rect` tap loop | **LANDED** | `7f549df2` — `perf(2d): inline channel math in emu_draw_blur_rect tap loop`; +11/-5 on `backend_emu_adv.spl` | **~12M interpreted dispatches removed** for one 160×90 r=6 blur (commit body). The plan's "~3.4x" multiplier is **not stated in the commit** — treat the dispatch count as the verified figure. Parity harness rows stayed `== 0`. |
| **GUI-1** persistent `Engine2D` (create once, `clear`+redraw per frame) + **GUI-5a** present-only-on-dirty | **LANDED** (via task #17) | `a7b57550` — `feat(2d/wm): persistent Engine2D GPU sessions`; showcase + `compositor_engine2d.spl` + `hosted_entry.spl` + `backend_metal.spl` | Raster-bound **176x–684x** vs per-frame create+shutdown (`doc/00_llm_process/feature_expert/wm_gui_window_drawing/skill.md:300-307`). Gates `engine2d_gpu_offload_contract_spec` 11/11, `engine2d_shared_raster_parity_spec` 21/21. |
| **GUI-2** drop startup 64×64 probe `Engine2D` in `emit_renderer_log` | **REJECTED** | no landing commit; rationale in this plan only | Micro-win (one startup construct+shutdown); superseded by GUI-1 making per-frame engine churn the real cost. Not worth a separate change; fold into any future showcase cleanup if that file is touched. |
| **2D-5** cache `glyph_rows_for_char` per-glyph bitmap | **REJECTED** | no landing commit; rationale in this plan only | Deferred: `glyph_bitmap_5x7.spl` is shared by engine2d + browser paint; the safe output-preserving version needs a one-time packed-table read that risked colliding with concurrent D2 work. Re-open as a next-wave item only if text-heavy frames are shown to dominate a real workload. |

> Anchor correction: the brief cited a "#17 report … ~8% WM composite" figure. The **176-684x**
> raster number is real (commit `a7b57550` + skill file). The **~8% WM-composite share** figure
> is **not present anywhere in the tree** (doc/09_report, git bodies, evidence spl) and has been
> dropped rather than guessed.

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

## Next wave (live backlog — fully specified)

Each item: motivation+evidence · files · steps · specs · gates · size (S/M/L) · deps · risk+rollback.
D2 reference: `doc/05_design/ui/rendering/draw_ir_multibackend_design.md` §D2 —
`SharedRaster`/`backend_emu` is the parity oracle; any pixel-changing edit must flip the assertion
through `test/02_integration/rendering/engine2d_shared_raster_parity_spec.spl`.

### N1 — Residual `compute_styles` superlinear (post-WEB-2) — **LANDED (dict fix) 2026-07-07, root cause re-attributed**

- **Motivation + evidence.** WEB-2 removed the `build_rule_buckets` dedup quadratic but
  `compute_styles` is still superlinear: 3000 distinct-class rules cost ~3.8× the time for 4.3×
  the rules *after* the fix (`doc/08_tracking/bug/web_compute_styles_residual_quadratic_2026-07-06.md`).
  A standalone probe verified `Dict<text,i32>` itself is linear, so the residual is elsewhere.
  Named suspects in the bug doc: `style_rule_candidates`
  (`simple_web_html_layout_renderer.spl:4924`) and the per-node matching loop in `compute_styles`
  (`:5259`).
- **Files.** `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`
  (owned by the `fix-web` lane — still disjoint from other agents).
- **Steps.** (1) Instrument the two suspects to attribute the residual (per-node candidate count ×
  rule count). (2) If `style_rule_candidates` rescans all rules per node, index candidates by the
  node's id/class/tag through the bucket structure WEB-2 already builds (reuse `entry_*` arrays)
  so each node consults only matching buckets. (3) Confirm cascade order preserved.
- **Specs.** Keep green: `test/02_integration/rendering/simple_web_css_cascade_spec.spl`,
  `test/01_unit/app/ui/browser_backend_pixel_paths_spec.spl` (both lock cascade order); re-run the
  distinct-class scaling probe → `compute_styles_ms` linear.
- **Gates.** Those two specs; `check-ui-backend-isolation.shs` (no new `rt_*`).
- **Size:** M. **Deps:** none (WEB-2 landed). **Risk+rollback:** cascade-order regression → the two
  specs catch it; rollback = revert to the post-WEB-2 state (still correct, just superlinear).
- **Outcome (2026-07-07).** Step (2) landed: `RuleBuckets` now carries `id_key_dict` /
  `class_key_dict` / `tag_key_dict` (the dicts `build_rule_buckets` already builds) through to
  `style_rule_candidates`, replacing the linear `text_key_index` scan with O(1) `dict_key_index`
  lookup. Component cost (candidates_ms) is now negligible, ~0.03–0.05 ms/node. Both cascade specs
  stayed green (3/3); `simple_web_css_cascade_spec.spl` output byte-identical pre/post-fix.
  **However the end-to-end `compute_styles_ms` total was unchanged** — the dominant cost was never
  the candidate lookup at the scale measured. Root cause re-attributed to the runtime
  `text.substring()` primitive scaling with start offset (O(offset) per call, not slice length),
  which made `parse_html` itself quadratic (1573→6972→26641 ms at N=700/1500/3000 — larger
  than `compute_styles` at N=3000) and left a residual ~2.5x-per-2x-N superlinearity in
  `compute_styles` (5417/13241/32995 ms) via the same lazily-substring-backed node fields
  (`nd.tag`/`class_attr`/`class_words`). See
  `doc/08_tracking/bug/text_substring_o_offset_parse_html_quadratic_2026-07-07.md`.
  **`parse_html` leg — LANDED 2026-07-07.** `_html_scan_events` rewrite: one native
  `text.split("<")` event stream consumed by a two-pass `parse_html` (no per-position
  `text.substring(pos, ...)` calls, so the O(offset) runtime primitive is off the hot path).
  Opus-reviewed CLEAN, 23/23 semantic fixtures byte-identical. Measured **27.3s → 1.1s at
  N=3000 (~24x)**; linearity confirmed 2.02–2.03x cost-per-doubling out to N=6000 (vs the prior
  ~2.6-4.3x superlinear ratios). `count_html_nodes` + 2 helper fns deleted (folded into the
  single-pass scanner). **Correction to the fix-direction note above:** a byte-array (`[u8]`)
  scan of `parse_html` was prototyped and measured **~10x worse** than the baseline under the
  interpreter — per-element `[u8]` reads dominate cost there just as they do in the
  `css_bytes_*` helpers (see `doc/08_tracking/bug/css_bytes_helpers_dead_code_2026-07-07.md`).
  The idiom that actually wins under the interpreter is one native `split()`/`substring`-free
  event scan plus small segment slices, not a byte-array walk. `compute_styles` itself is
  **unchanged and still open** — its residual superlinearity lives in the selector-match chain
  (`style_rule_candidates`/cascade matching), not in parse-side node-field construction; do not
  attribute it to parse_html lazy views.

### N2 — Separable box blur (2-pass)

- **Motivation + evidence.** ~6× on top of 2D-1 for large radii (2D Rank 1 (3)). Pixel-changing:
  integer-division rounding of a true 2-pass differs from the current single-pass tap sum.
- **Files.** `backend_emu.spl` (D2-hot) + the D2 canonical reference + parity spec.
- **Steps.** (1) Wait for the D2 consolidation to settle on `backend_emu.spl`/parity spec. (2)
  Implement 2-pass; (3) regenerate the D2 canonical reference; (4) **flip** the parity-harness blur
  assertion to the new reference (this is the one place a pixel change is sanctioned).
- **Specs.** `engine2d_shared_raster_parity_spec.spl` blur rows updated (not `== 0` — new
  reference); perf assertion (single large-radius blur under a wall-clock ceiling).
- **Gates.** Parity spec (post-update), `check-engine2d-gpu-offload-evidence.shs`.
- **Size:** M. **Deps:** D2 settled; sequence after N-region (N3) if both land, to share the
  read_pixels floor removal. **Risk+rollback:** parity drift on other ops if the reference regen is
  too broad → regen only blur/shadow rows; rollback = revert to single-pass (2D-1 state).

### N3 — Region / dirty-rect readback

- **Motivation + evidence.** `read_pixels()` is a full-canvas floor (~0.86s in the 2D-1 blur case;
  also the WM present path). `read_pixels_region(x,y,w,h)` removes it; also unblocks the WM
  dirty-tile present and item B (motion background) in the WM plan.
- **Files.** `src/lib/gc_async_mut/gpu/engine2d/backend.spl` (`RenderBackend` trait, add
  `read_pixels_region`), `backend_software.spl` (D2-hot), `src/os/compositor/compositor_engine2d.spl`
  (`present_rect` honoring its rect args + region readback), `display_backend.spl`
  (`CompositorBackend.present_rect` already exists `:19` — make it real).
- **Steps.** (1) Add `read_pixels_region` to `RenderBackend` + software impl (after D2). (2) Make
  `Engine2dCompositorBackend.present_rect` (`compositor_engine2d.spl`) honor rect args instead of
  full present. (3) Compositor marks dirty regions; present loop reads back only dirty tiles.
- **Specs.** Parity harness stays `== 0` for full-frame; add a region-readback correctness spec
  (region == corresponding sub-rect of full read). WM: `check-hosted-wm-capture-evidence.shs`.
- **Gates.** Parity spec, hosted-WM capture, offload evidence.
- **Size:** L. **Deps:** D2 settled; ties into WM plan item B/E (this is the method most likely to
  force the CompositorBackend/RenderBackend decision in that plan's item E). **Risk+rollback:**
  trait addition touches every backend impl → add as a defaulted method (full-frame fallback) so
  non-updated backends still compile; rollback = fallback path is the current behavior.

### N4 — `draw_gradient_rect` one-pass

- **Motivation + evidence.** 6.16× per-px vs a plain fill (2D Rank 4).
- **Files.** `backend_emu.spl` (D2-hot); may reverse the just-landed sw→emu delegation.
- **Steps.** D2-aligned decision first: shared one-pass in `backend_emu` **or** a documented
  software override (mirroring the `draw_line` exception in the D2 design). Then implement +
  parity.
- **Specs.** Parity harness gradient rows (`== 0` if output-preserving; else flip like N2).
- **Gates.** Parity spec. **Size:** M. **Deps:** D2 decision. **Risk+rollback:** reversing sw→emu
  delegation could regress other callers → gate on the parity spec; rollback = revert to delegation.

### N5 — Bulk `clear`/`read_pixels` memset/memcpy + real `cpu_simd` backend

- **Motivation + evidence.** 50-200× at HD for bulk clear/readback (2D Rank 2/3). **Blocked** on
  the mutable-array-extern bridge: the interpreter extern bridge cannot mutate `Value::Array`
  in place, so `rt_array_fill_u32` / `rt_engine2d_simd_*` cannot write back
  (`doc/08_tracking/bug/cpu_simd_mutable_array_extern_wiring_2026-05-31.md`, OPEN). The **same bug
  doc** records a 2026-07-06 honesty audit: today's `cpu_simd` backend is a **plain alias of scalar
  `cpu`** with no live SIMD dispatch — see N6.
- **Files (for the seed owner).** The interpreter extern bridge (mutable-array write-back),
  `rt_array_fill_u32`/`rt_engine2d_simd_*` runtime externs; Simple side afterwards in
  `backend_software.spl` / a real `cpu_simd` backend.
- **Steps.** (1) Seed: land the mutable-array-extern write-back bridge. (2) Wire bulk clear/readback
  through it. (3) Only then a real `cpu_simd` backend (N6).
- **Specs.** Parity harness `clear`/`read_pixels` rows stay `== 0`; perf assertion HD clear/readback
  under a ceiling.
- **Gates.** Parity spec. **Size:** L (seed). **Deps:** mutable-array-extern bridge (seed).
  **Risk+rollback:** none until the bridge lands (item is parked); rollback = scalar path (current).

### N6 — Real SIMD backend honesty (fake-counter removal)

- **Motivation + evidence.** The 2026-07-06 audit in
  `cpu_simd_mutable_array_extern_wiring_2026-05-31.md` found `cpu_simd` is an alias of scalar `cpu`
  — it must not advertise SIMD it does not run (project rule: no fake evidence / no greenwashed
  counters). NEON/SSE2 row kernels DO exist for the real path (`simd_fill_row` →
  `rt_simd_fill_row_u32`, per backend-isolation anchors), but the `cpu_simd` *backend selector*
  does not dispatch to them.
- **Files.** The `cpu_simd` backend selection path + any SIMD-usage counter it exposes.
- **Steps.** (1) Until N5's bridge lands, make `cpu_simd` **either** dispatch to the real
  `simd_fill_row` kernels where the extern already supports it **or** report honestly that it is
  scalar (no fake SIMD counter). (2) After N5, wire the genuine SIMD span ops.
- **Specs.** A spec asserting the reported backend/counter matches the code path actually taken
  (no "SIMD used" when scalar). **Gates.** Parity spec; the honesty spec. **Size:** S (honesty) /
  M (real dispatch). **Deps:** real dispatch depends on N5. **Risk+rollback:** low; rollback =
  keep the honest-scalar report.

### N7 — Metal default-on criteria

- **Motivation + evidence.** Metal is not default-on. The persistent-session raster win is large
  (**176x-684x**, commit `a7b57550`; skill `:300-307`), but that is the CPU raster path, not proof
  Metal should be the default backend. Two criteria must be met before flipping the default:
  1. **Universal one-call upload/readback** — the `rt_write_u32s_to_raw`/`rt_u32s_from_raw` runtime
     externs must be wired (currently `SIMPLE_ONE_CALL_READBACK=1` crashes: `unknown extern
     function: rt_write_u32s_to_raw`), then bit-exact vs the per-pixel path, before flipping
     `SIMPLE_ONE_CALL_READBACK` default-on. Without it, per-primitive marshalling makes Metal lose
     to CPU on small frames. (Seed/runtime-extern change — off the pure-Simple path.)
  2. **WM content lane no longer the dominant cost** — Metal default-on is only worth it once the
     composite/content lane, not the backend, bounds the frame. (The specific "~8% WM composite"
     share once cited for this is **not recorded in-repo** and must be re-measured before it can
     gate anything.)
- **Files (seed).** `rt_write_u32s_to_raw`/`rt_u32s_from_raw` runtime externs; then the default
  backend selector.
- **Steps.** (1) Seed wires the one-call externs. (2) Bit-exact verify vs per-pixel. (3) Re-measure
  the WM composite share (replace the missing ~8% figure with a real number). (4) Only if both
  criteria pass, flip the default + add a regression gate.
- **Specs.** Bit-exact one-call vs per-pixel readback spec; the four perf non-regression seams
  (Metal no-mirror, batched Metal FFI, NEON/SSE2 kernels, `WebRenderPixelArtifactCache`) stay
  green. **Gates.** Parity spec; `check-engine2d-gpu-offload-evidence.shs`. **Size:** L (seed +
  measurement). **Deps:** one-call externs (seed). **Risk+rollback:** flipping the default could
  regress small-frame/idle cases → gate on the re-measured composite share + bit-exact proof;
  rollback = keep Metal opt-in (`SIMPLE_GUI_BACKEND`).

### N9 — CPU/GPU dual-algorithm mechanism + GPU-dict pilot (cross-ref)

- Per-op two-algorithm-set selection (CPU bulk-idiom variant vs GPU kernel) and a buffer-backed GPU
  dictionary primitive are specified in
  `doc/03_plan/ui/rendering/cpu_gpu_dual_algorithm_plan.md`
  (research `doc/01_research/ui/rendering/cpu_gpu_dual_algorithm_research.md`, design
  `doc/05_design/ui/rendering/cpu_gpu_dual_algorithm_design.md`). Its W6/W7 are this plan's
  N5/N6; its W1 (upload-only Metal palette LUT) is a new no-seed first-wave item; its W2 lint
  enforces the "no per-element loop on CPU hot paths" contract these measurements motivate.

### N8 — Winit `[u32]` FFI signature / Web parse-artifact cache (parked)

- **Winit `[u32]` FFI** (GUI Rank 5b): halves marshalled bytes; Rust extern change (seed). Parked.
- **Web parse-artifact cache** (Web Rank 3): re-evaluate only if a non-identical-but-reparseable
  workload is demonstrated (identical-content is already covered by the landed `#15`
  `WebRenderPixelArtifactCache`). Parked.

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
