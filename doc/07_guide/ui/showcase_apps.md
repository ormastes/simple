# Running the GUI, web, and 2D showcases

The canonical app IDs are `graphics_2d_showcase`, `web_standards_showcase`, and `gui_widget_showcase`. Readiness is recorded in `src/lib/common/ui/showcase_catalog.spl`; **all nine `standalone_ready`/`host_wm_ready`/`simpleos_wm_ready` bits are still `false`** (correct — no surface has full deployed-binary + real-render + post-input proof yet).

## Resolution/DPI convention (landed 2026-07-12)

All four showcase entry points — `graphics_2d_showcase(_gui).spl`, `widget_showcase_gui.spl`, `web_render_file_gui.spl`, `web_standards_showcase_gui.spl` — now share one resolution/density convention, read via `env_get`:

- `SHOWCASE_RESOLUTION`: unset or `"4k"` => **3840x2160 (DEFAULT)**; `"8k"` => 7680x4320; an explicit `"WxH"` token (e.g. `"320x240"`) => that exact size.
- `SHOWCASE_DPI`: default **300**. For `graphics_2d_showcase(_gui).spl` and `widget_showcase_gui.spl` it actually scales stroke width/detail/glyph size (a permille scale factor vs. a 96-DPI baseline, `sc()`/`sc1()`). For the web renderer it is **read and reported only** (`dpi=<value> dpi_scale_applied=false` in the status line) — the shared HTML/CSS layout engine has no device-pixel-ratio hook; see `doc/08_tracking/bug/web_render_dpi_scaling_unsupported_2026-07-12.md`.

**The default changed from small (e.g. 800x600/640x480) to full 4K.** Every source file's own header comment says the same thing: full 4K/8K rendering is **compiled-lane-gated** — the tree-walking interpreter is far too slow for millions of software-rasterized pixels. Verify parameterization at a small explicit rung instead, e.g. `SHOWCASE_RESOLUTION=320x240`.

## Deployed-binary caveat

`bin/simple` (the symlinked `bin/release/aarch64-apple-darwin/simple`) still traps `exit=132 "runtime error: field access on nil receiver"` on dict-heavy compiles (`doc/08_tracking/bug/stage4_compiled_dict_no_growth_2026-07-11.md`); Stage-4 has not been rebuilt/redeployed with the fix. **Every command below that needs the fix uses the fresh-seed binary (`src/compiler_rust/target/bootstrap/simple`) explicitly** — do not assume `bin/simple` reproduces these results.

## Standalone

Fresh-seed commands, small explicit resolution (fast, verifies the resolver + a real render without paying 4K interpreter cost):

```text
SIMPLE_LIB=src SHOWCASE_RESOLUTION=320x240 src/compiler_rust/target/bootstrap/simple run examples/06_io/ui/graphics_2d_showcase.spl
SIMPLE_LIB=src SHOWCASE_RESOLUTION=640x480 src/compiler_rust/target/bootstrap/simple run examples/06_io/ui/web_render_file_gui.spl examples/06_io/ui/browser_common_elements_showcase.html
SHOWCASE_PPM=/tmp/widgets.ppm SIMPLE_LIB=src SHOWCASE_RESOLUTION=1280x720 src/compiler_rust/target/bootstrap/simple run examples/06_io/ui/widget_showcase_gui.spl
```

Deployed-binary (`bin/simple`) equivalents remain useful as *reproductions of the blocked state*, not PASS claims, until redeploy — see `graphics_2d_showcase_nil_receiver_2026-07-11.md` / `web_render_file_gui_nil_receiver_2026-07-11.md`.

**Per-app lane reality, grounded in each landing commit's own message:**

- **`graphics_2d_showcase`** (`2076527bb1`): small-rung render verified varied (bbox fills 95%/98% of canvas); full 4K is compiled-lane-gated (not measured/claimed at 4K under the interpreter).
- **`gui_widget_showcase`** (`9b42b2011d`): verified varied content across all 4 layout quadrants at 720p (69,320 content px); full 4K is native/compiled-lane-gated — **interpreter throughput ~5k px/s**, so a full 3840x2160 frame (~8.3M px) is a minutes-to-hours proposition under the tree-walking interpreter.
- **`web_standards_showcase`** (`297815ba0a`): verified real varied content at 640x480 (82 distinct colors). **HONEST: at 4K the interpreter output degrades to a uniform, background-color-only frame** — a real budget/perf-wall bug, not a rendering-logic bug (`doc/08_tracking/bug/web_render_budget_env_override_ignored_by_stage_rearm_2026-07-12.md`, filed alongside this commit). **That bug's own doc says "Status: Fixed", but the actual 8-line engine fix is NOT present in the pushed/committed source at this repo's HEAD** — the commit message says it explicitly: *"the 8-line engine fix commits separately (WC currently contaminated by a peer layout refactor)"*. Verified directly: `git show HEAD:src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl` still has the un-overridden `budget_us` rearm logic; the fixed version exists only in this working tree's uncommitted `M` state. **Treat the web-4K-uniform-frame bug as still OPEN at the pushed commit**, not fixed, until a follow-up commit lands it cleanly.

Full 4K web rendering's real fix is architectural, not a budget tweak — see `doc/03_plan/ui/webir_drawir_optimization.md` (WebIR/DrawIR incremental-repaint plan, committed `3963a47`).

## Host WM

Three filesystem-child-bridge adapters exist, all using the same pattern (`src/lib/common/ui/wm_app_process_contract.spl`: spawn the standalone source as a `SIMPLE_WM_APP_MODE=client` child, exchange bridge/frame/event files, blit the child's PPM into the host compositor window):

```text
SIMPLE_GUI=1 scripts/gui/macos-gui-run.shs examples/06_io/ui/wm_widget_showcase_gui.spl
SIMPLE_GUI_RUN_SKIP_NUDGE=1 scripts/gui/macos-gui-run.shs examples/06_io/ui/wm_graphics_2d_showcase_gui.spl
SIMPLE_GUI_RUN_SKIP_NUDGE=1 scripts/gui/macos-gui-run.shs examples/06_io/ui/wm_web_standards_showcase_gui.spl
```

- **`wm_graphics_2d_showcase_gui.spl` (2026-07-12):** the client render path had a real cross-module bug — `run_wm_client_graphics_2d()` called `draw_showcase(engine)` through `use graphics_2d_showcase.{run_graphics_2d_showcase, draw_showcase}`, and the import leaked `graphics_2d_showcase`'s own `draw_showcase`/`label` symbols into scope, shadowing local same-named copies and silently mutating a discarded instance — a blank 800x600 frame (0/1,440,000 nonzero). Fixed by renaming the two colliding local functions to `wm_draw_showcase`/`wm_label`; verified 1,439,967/1,440,000 nonzero. Full detail and the still-open compiler root cause: `doc/08_tracking/bug/cross_module_imported_fn_mutation_not_propagating_2026-07-12.md`. **That verification was at 800x600 (an explicit small resolution), not the new 3840x2160 default** — no report shows this client path launched successfully at the new default.
- **`wm_web_standards_showcase_gui.spl`:** the old "fixed 80x60" limitation noted in earlier drafts of this doc is **obsolete** — the child now calls `showcase_resolution_dims()` like the standalone app, so `RW`/`RH` default to 3840x2160.
- **Important caveat, all three adapters:** none of `wm_graphics_2d_showcase_client_env` / `wm_web_standards_showcase_client_env` (in `wm_app_process_contract.spl`) sets `SHOWCASE_RESOLUTION` for the spawned child, and `widget`'s `run_wm_client()` calls `build_wm_pixels(W, H, ...)` with the hardcoded module-level `W=3840, H=2160` directly (not the resolver at all). **So by default, launching any of the three host-WM adapters today attempts a full 4K child render** — under the interpreter (the only lane the fresh seed reaches; `bin/simple` is still blocked), this hits the same "compiled-lane-gated" wall described above. To reproduce quickly, export `SHOWCASE_RESOLUTION=<small>` before launching the wrapper script, or (graphics only) set `SHOWCASE_DRY_RUN=1` to verify the resolver without paying the render cost.
- No adapter has a committed launched/interaction GUI-evidence run (snapshot/find/act/history + framebuffer + provenance) in this repo as of this writing — do not cite `host_wm_ready` until that lands. The widget adapter's pattern is the longest-accepted one, but the most recent dedicated evidence found for it (`doc/09_report/gui_showcase_launch_evidence_2026-07-06.md`) shows it **BLOCKED** under parallel-agent load, predating today's 4K-default change — do not assume it currently launches cleanly at the new default without re-verifying.

## SimpleOS/QEMU

No showcase entry is accepted in the installed SimpleOS launcher yet. A valid result must show the installed `/sys/apps/*_showcase.smf` identity, guest PID/window ownership, nonblank guest framebuffer, and a post-input state/pixel change. Host wrappers and fixed serial markers are insufficient.

**2026-07-12: the WM now boots a real 4K (3840x2160, argb8888) screen** (`603fabe601`), independent of the showcase apps themselves:

- `gui_entry_desktop.spl`'s framebuffer went 1024x768 -> 3840x2160 argb8888; QEMU gained `-global VGA.vgamem_mb=64`.
- **Root cause fixed:** `rt_alloc` and `rt_alloc_zeroed` silently truncated any allocation over 16MB down to 16MB while still reporting success, so the 33.2MB 4K backbuffer silently overflowed into adjacent heap, causing a boot fault-storm. Both clamps were removed (a malloc panic-on-exhaustion against the real 192MB `_heap[]` is the correct limit, not a silent truncation).
- The commit message reports the harness (`scripts/check/check-simpleos-wm-fullscreen-evidence.shs`) as `status=pass`: scanout `3840x2160` stride `15360` argb8888, `baseline_ppm=24883217 bytes`, `changed_bytes=23174856`, `baseline_sha256==restored_sha256`, maximize/restore markers intact.
- **Discrepancy found during this verification pass (flagged, not papered over):** the committed `doc/09_report/simpleos_wm_fullscreen_evidence_2026-07-12.md` still shows `status: fail, reason: dynamic-scanout-or-desktop-readiness-missing` with 0-byte PPMs — a stale snapshot from a different run in the same session, not the passing run the commit message describes. **A live rerun of the same harness during this verification pass also produced `status=fail`** with the correct scanout (`3840x2160`, stride `15360`) but zero-byte baseline/maximized/restored PPMs (`build/simpleos_wm_fullscreen_evidence/evidence.env`), the same failure signature as the stale committed report. The PASS state with `changed_bytes=23174856` and the sha256 round-trip described in the commit message **could not be independently reproduced in this pass** — it rests on the commit message's own claim, not on a currently-reproducible run or a currently-committed evidence file. Treat it as reported-not-currently-verifiable until a fresh passing run is captured and the report regenerated.
- **8K (132MB VRAM) is beyond BGA/std-vga capability** — explicitly filed as a follow-up, not attempted.
- A freestanding-codegen bug was hit and worked around while making the resolution a named constant: hoisting `val DESKTOP_FB_WIDTH_4K: u32 = 3840` to module level and reading it from `spl_start()` corrupts the value to garbage (`width=16000 height=1048`) under the `x86_64-unknown-none` Cranelift freestanding target; plain local `u32` literals do not. Filed: `doc/08_tracking/bug/x64_freestanding_module_level_val_u32_desktop_gui_2026-07-12.md`. Workaround (local literals) is what's actually deployed.

This fix is about the guest's raw framebuffer size and QEMU scanout, not about the three showcase apps specifically. **Installed showcase apps in SimpleOS still show SHELL-MATERIALIZED content, not real in-guest app render** — ring-3 own-render for these apps remains an unfinished frontier (see `doc/08_tracking/bug/browser_demo_frozen_loading_placeholder_2026-07-12.md` for one concrete instance: `browser_demo_hosted_main` calls `update_content` exactly once and never again). `simpleos_wm_ready` therefore stays `false` for all three showcases.

**De-fake (commit `599760ca16`, pre-dates today's 5 commits but still current):** WM content frames route through the real HTML/CSS engine (`simple_web_content_frame_cached` uses `cache.request_to_pixel_artifact`) instead of a tag-strip heuristic, now fallback-only with rejectable provenance. This is real but costly: the full engine is measured **~55-60x slower per re-render** than the old tag-strip fallback under the interpreter (`doc/08_tracking/bug/web_render_full_engine_content_frame_reroute_perf_2026-07-12.md`) — the motivating cost behind the WebIR/DrawIR plan below.

## The path to feasible interactive 4K/8K web

`doc/03_plan/ui/webir_drawir_optimization.md` (committed `3963a47`, 236 lines, draft/not-yet-executed) lays out the concrete plan: `simple_web_layout_render_html_draw_ir` (Path B, DrawIR emission) already exists as a thin/incomplete alternative to the full pixel-paint path (Path A); `draw_ir_diff.spl`'s node-level diff (`draw_ir_diff_compositions`) already exists and is spec-tested but has **zero production render-loop callers**. The plan's headline: wire that diff into the content-frame render loop so repaint cost scales with changed-node count, not total pixel count — the identified path to feasible interactive 4K/8K web, not yet executed.

## Verification flow

For each ready surface: open the catalog, launch the app, snapshot the visible window, find a labeled control/section, act through the real input route, inspect event history, capture the post-action semantic state, and retain the same-run framebuffer/readback plus backend provenance. Blank frames, source-only assertions, synthetic GPU handles, and action logs without a changed frame/state fail verification.
