# Feature: rendering-inside-rendering

## Raw Request
with spipe dev skill, while do bootstrap, lets do, rendering inside rendering, harden web rendering, 2d, and gui.
1. 2d rendering to have internal rendering embedded.
2. web rendering to embed web rendering inside web rendering (if std not supported hidden private feature) it might use 2d internal embedding rendering.
3. let gui rendering embedding gui panel and let embed web rendering panel. it might use last web rendering embedding. and gui internal window and objects might use it also.
each web rendering might separate space in default or share it. research what other tools done similar problems. and update wm by change interface of gui,web,2d. and 3d if needed (embedding 3d objects in 3d object).
and finally simple web browser buttons, gui, text fields rendering check with it.

## Task Type
feature

## Refined Goal
Add a uniform nested-render-surface capability across the pure-Simple rendering stack: (1) 2D renderer gains an internal embedded render target (render sub-scene offscreen, composite into parent); (2) web renderer gains web-in-web embedding (iframe-like; hidden private feature if not std-supported), built on the 2D embedding primitive, with each embedded web instance in a separate space by default and optionally shared; (3) GUI rendering gains panel-in-panel embedding and web-render panels, reusable by WM internal windows/objects; WM/gui/web/2d (and 3d object-in-object if needed) interfaces updated coherently; verified end-to-end by rendering checks of the simple web browser's buttons, GUI chrome, and text fields.

## Acceptance Criteria
- AC-1: 2D renderer exposes an embedded-render-target primitive: render a child draw-IR scene/command list into an offscreen surface and composite it into a parent scene with position/clip/transform, on the CPU lane (GPU lane if already offscreen-capable).
- AC-2: Web renderer can embed a web rendering inside a web rendering (iframe-like element or private equivalent), where the child page renders through its own pipeline instance into an embedded 2D surface composited at its layout position.
- AC-3: Each embedded web rendering runs in a separate space (own document/JS context) by default with an explicit opt-in to share space with the parent; the switch is tested both ways.
- AC-4: GUI rendering supports embedding a GUI panel inside a GUI panel and embedding a web-rendering panel inside a GUI panel; WM internal windows/objects can consume the same embedding primitive.
- AC-5: WM interfaces for gui/web/2d are updated to carry nested render surfaces coherently (no parallel one-off paths); 3d object-in-object embedding addressed if the 3d scene graph lacks it.
- AC-6: Prior-art research (browsers/OOPIF, Wayland subsurfaces, Godot SubViewport, Flutter platform views, render-to-texture) is documented under doc/01_research and reflected in the design decisions (esp. separate-vs-shared space semantics).
- AC-7: Simple web browser chrome verification: buttons, GUI elements, and text fields render correctly via the new embedding paths, with fail-closed pixel/structure evidence (no placeholder passes).
- AC-8: Bootstrap keeps running in parallel; the `build bootstrap` entry-point regression is fixed or concretely tracked.

## Scope Exclusions
Out-of-process isolation (separate OS processes per embedded web instance) is excluded; "separate space" means separate in-process document/layout/JS contexts. Physical-board evidence excluded.

## Research Summary
### 2D stack (agent report)
- Engine2D facade: `src/lib/gc_async_mut/gpu/engine2d/engine.spl:76` (canonical copy; mirrors in gc_sync_mut + nogc lanes). Backend trait: `engine2d/backend.spl:57` (`RenderBackend`: init/clear/draw_*/draw_image[_blend|_scaled|_transform]/set_clip/set_mask/present/read_pixels/width/height).
- Draw IR: `src/lib/common/ui/draw_ir.spl` — `DrawIrCommand`:59, `DrawIrBatch`:88, `DrawIrComposition`:96, **`DrawIrEmbeddingConfig`:48** (surface_id, component_id, x,y,w,h, layer, opacity_milli, clip) — schema already models embedding.
- Executor gap: `engine2d/draw_ir_adv.spl:275-392` interprets embedding as translate+clip ONLY; surface_id/layer/opacity_milli carried but NOT honored. No real offscreen surface.
- Existing partial offscreen: CPU `compositor.spl` `Layer`(:16, passive pixels)+`Compositor.composite_to_buffer`(:124); OpenGL single main FBO (`backend_opengl.spl:70`, sffi `opengl_sffi.spl:89`); Skia `SkSurface` w/ GpuStub (`src/lib/skia/entity/surface.spl:26`) disconnected from Engine2D; de-facto pattern = second Engine2D + read_pixels + draw_image (`bridge_drawing_compositor.spl:82-90`).
- WM executor: `window_scene_draw_ir.spl:577` `shared_wm_scene_render_to_backend` draws every window directly into single shared `CompositorBackend` (`src/os/compositor/display_backend.spl:9`); `window_surface_registry.spl` surface_id→window is metadata only. Bridge: `compositor_engine2d.spl:23` Engine2dCompositorBackend.
- Insertion plan (CPU first): `Engine2D.create_offscreen(w,h)` near engine.spl:146; `draw_engine(dst_x,dst_y,src)` = draw_image_blend(read_pixels); honor DrawIrEmbeddingConfig in draw_ir_adv.spl (offscreen per surface_id, blit with opacity/layer). GPU: capability-gated create_offscreen/set_render_target/draw_render_target on RenderBackend w/ emu fallback; OpenGL FBO ready, Metal/Vulkan stubbed.
- Test home: `test/02_integration/rendering/engine2d_render_surface_matrix_spec.spl` (pending stubs); no existing embedding tests.

### GUI/WM/3D (agent report)
- Three-tier pipeline: model (`common.ui`) → projection (SharedWmScene/Draw IR) → executor (CompositorBackend). Universal content contract = `WmContentFrame` (flat ARGB) at `window_scene.spl:275` (window_id, scene_revision, content_revision, origin_kind, w, h, pixels, checksum); only origin defined = `WM_CONTENT_ORIGIN_SIMPLE_WEB` (:271).
- Widget tree IS hierarchical (`widget.spl:8-29` register_widget_child etc.); WindowManager/ManagedWindow flat (`window.spl:18,31`); SharedWmWindow flat (`window_scene.spl:12`); SharedWmScene flat (:294); SharedWmRenderInput (:303).
- Content flow/frame: `HostCompositor.render_frame()` `host_compositor_entry.spl:560` → per window `simple_web_content_frame_cached` (`simple_web_window_renderer.spl:165`) → frames → `shared_wm_scene_render_taskbar_context_to_backend` (`window_scene_draw_ir.spl:554`) → `_shared_wm_content_frame_for_window`:504 (strict revision/checksum/size; hard-codes simple_web origin) → `blit_pixels` at :538; invalid frame → magenta fill :542 (fail-closed).
- Draw IR embedding vocabulary exists but unused in WM path: DrawIrEmbeddingConfig per batch, DrawIrCommand.parent_id always "" (`window_scene_draw_ir.spl:193/205/220`).
- 3D: engine3d backends only, NO scene graph; app model `src/app/model3d/main.spl` Node3:60/Scene3:67 flat. 3D-in-3D = greenfield (children+transform on Node3).
- Evidence pattern: `scripts/check/check-simpleos-wm-fullscreen-evidence.shs` (reject rust-seed → native-build → QEMU+QMP → serial scanout-evidence markers → pmemsave pixel capture → input inject → SHA before/after → evidence.env + doc/09_report, fail-closed). New work: analogous embedded-surface evidence script.
- Minimal WM change set: (1) WmContentFrame += parent_window_id + offset_x/y; (2) origin_kind add GUI/ENGINE3D + generalize validation; (3) executor recursion over child frames w/ clip to parent rect (blit_pixels unchanged); (4) thread DrawIrEmbeddingConfig/parent_id in _wm_draw_ir_window_batch (:218); (5) producers: web child-frame variant + GUI UITree→frame + 3D Scene3→frame; (6) optional Node3 children.

### Web stack (agent report)
- Production engine: `src/lib/gc_async_mut/gpu/browser_engine/` — real path is `simple_web_html_layout_renderer.spl` (9.2k lines, parallel-array parse→style→layout→paint into flat [u32] fb). Entry: `simple_web_layout_render_html_software_pixels(html,w,h,budget_ms)`:9027; `..._at_scroll`:9202; gpu frame:9161; draw_ir:8956; internal `paint(...)`:8383; `parse_html`:651. Facade: `simple_web_renderer.spl:83`.
- Second display-list engine: `src/lib/common/render_scene/` (LayoutBox/BoxKind, PaintOp/DisplayList) used by `src/app/ui.browser/renderer.spl` (`paint_layout_box`:216 recursive).
- iframe support: NONE (only `embed` as void tag). Closest analog = replaced-element `img`/`input` path at layout_renderer:7475; pixel-carrying paint primitive exists: `PaintCommand.image` (`paint.spl:48`) + "image" PaintSceneCommand w/ pixels.
- Web→WM: `simple_web_window_renderer.spl:165` → WebRenderArtifact pixels (`web_render_api.spl:89`) → WmContentFrame. Everything is [u32] pixel blit.
- JS isolation unit: `BrowserRuntimeState` (`web/browser_session.spl:234`, one JsRuntime per document, created :246-255). Separate space = child BrowserRuntimeState/BrowserSession per iframe; shared = pass parent runtime/DOM in. No parent/child plumbing today.
- Browser chrome: `src/app/ui.browser/` app.spl/renderer.spl; window chrome HTML in simple_web_window_renderer. Specs: widget_input_textfield_spec, widget_button_checkbox_dropdown_spec, html_render_spec, simple_web_renderer_spec, browser_renderer_hit_test_events_spec.
- Iframe hook plan: parse iframe as replaced element (tree_builder + parse_html + NOT laid-out children), fixed box via w/h/CSS at :7475 path, paint = recursive render child html → offscreen [u32] → blit at box origin in paint():8383 (option: DrawSubScene PaintOp in render_scene engine); depth cap + budget share for safety.

## Architecture

### Decisions
- One conceptual RenderSurface pattern everywhere: render child content into an offscreen [u32] surface, composite into parent with position/clip/opacity. No new cross-layer type is required because WmContentFrame ([u32] ARGB) is already the universal contract; each layer realizes the pattern with its own existing vocabulary.
- Pixel path and input path stay separate (Flutter lesson); this arc changes the pixel path only, input routing into embedded surfaces is a recorded follow-up unless trivial.
- `space: separate|shared` is an attribute of the embedding element, orthogonal to placement. In the no-JS layout renderer: separate = child document styled only by its own CSS; shared = parent CSS rules also apply to child. In the JS/session path: separate = own BrowserRuntimeState; shared = parent runtime (follow-up if session wiring is large).
- Depth cap (3) and render-budget sharing for recursive web embedding; fail-closed magenta fill on invalid child frames (matches existing WM convention).
- WindowManager/ManagedWindow/SharedWmScene stay FLAT; nesting is expressed at the content-frame layer (parent_window_id + offset) and Draw IR embedding layer.

### Lane plan (disjoint files, parallel)
- Lane A (2D): Engine2D.create_offscreen + draw_engine composite primitive (engine.spl ~:146); honor DrawIrEmbeddingConfig.surface_id/opacity_milli/layer in draw_ir_adv.spl:275-392 with real offscreen Engine2D + blit-back. CPU lane first; GPU = capability-gated follow-up (OpenGL FBO ready). Sync identical engine2d mirrors.
- Lane B (web): iframe as replaced element in simple_web_html_layout_renderer.spl (parse_html:651, replaced-box like img:7475, recursive render→offscreen [u32]→blit in paint():8383), srcdoc + local src, space attr (separate default/shared), depth cap + budget share. Hidden/private: element handled without claiming std support.
- Lane C (WM/GUI): WmContentFrame += parent_window_id/offset_x/offset_y (window_scene.spl:275); origin_kind add GUI; generalize _shared_wm_content_frame_for_window:504; executor recursion w/ parent-rect clipping after :538; thread DrawIrEmbeddingConfig/parent_id at :218; child-frame producer in simple_web_window_renderer.spl; GUI UITree→frame producer.
- Lane D (3D): Node3.children + relative transform compose in src/app/model3d/main.spl (flat→tree, recursive render offset). Minimal.
- Lane E (verify, after A-C): specs green + browser chrome (buttons/text fields) rendering check using embedding; evidence fail-closed.
- Lane F (bootstrap): fix `build bootstrap` entry-point regression, keep bootstrap running (agent in flight).

## Phase
arch-done; impl-in-progress

## Implementation Progress
- Lane A (2D) DONE: engine.spl gains create_offscreen (transparent-init) + draw_engine/draw_engine_opacity + alpha-scale helper; draw_ir_adv.spl renders surface_id batches into real offscreen Engine2D w/ depth cap 3 + perf guard (skip offscreen for 0,0/full-opacity/full-size batches). New spec engine2d_embedded_surface_spec 5/5; regressions green (drawing 2/2, clip 3/3, draw_ir_adv 5/5, runtime_queue 1/1, wm_scene_metal_offload 4/4 bit-exact, ui_draw_ir_pipeline 6/6, nomirror mism=0). Side effect (intended): WM batches already set surface_id → opacity_milli=930 for unfocused windows now honored. Mirrors are re-export facades; nothing to sync.

## Log
- dev: Goal set via /goal; state file created with 8 acceptance criteria (type: feature).
- research: Launched 4 parallel agents (2d stack, web stack, gui/wm/3d interfaces, prior-art) + 1 bootstrap-regression fix agent. `bin/simple build bootstrap` fails with "No entry point specified for native-build backend" (known follow-up regression).
- bootstrap: `build bootstrap` entry-point regression root-caused (bootstrap subcommand fell through to generic native-build forward without --entry, src/app/build/cli_entry.spl). Fix ALREADY LANDED by parallel session in `5e9ace8c01db` (handle_build_bootstrap, in-process 3-stage + SHA compare). Current failure = deploy lag (bin/simple built 11:02 pre-fix; it also SIGBUSes on trivial native-build — RuntimeDict bug fixed in same commit). Two parallel sessions already running --deploy; we intentionally do not clobber. Script-path bootstrap verified: stage2/stage3 built OK in build/bootstrap_verify2. No changes made by our agent.
- research: Prior-art report landed at doc/01_research/domain/rendering_inside_rendering.md. Recommended: one RenderSurface primitive (owned bitmap/Metal texture + damage tracker + update mode) shared by 2d/web/gui; WM-level surface tree (sync/desync commits per Wayland subsurfaces, hit-testing, versioned SurfaceId lifecycle per Chromium viz); `space: separate|shared` flag per embedded instance (Godot SubViewport own_world analogue), orthogonal to process placement; input path separate from pixel path (Flutter texture-layer lesson).
