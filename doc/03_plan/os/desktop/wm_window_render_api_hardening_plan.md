# WM Window-Render API Hardening — Phase 2 Plan

**Status:** DRAFT (2026-07-07) · **Owner:** OS/desktop + UI/rendering · **Scope:** the
next hardening wave on top of the landed window-render executor.

**Reads-with:**
- Design: [`doc/05_design/os/desktop/simple_gui_internal_window_impl_spec.md`](../../../05_design/os/desktop/simple_gui_internal_window_impl_spec.md) (phase-2 provider design section)
- Design: [`doc/05_design/os/desktop/shared_wm_renderer_unification.md`](../../../05_design/os/desktop/shared_wm_renderer_unification.md)
- Sibling plan (backend isolation): [`doc/03_plan/ui/rendering/backend_isolation_plan.md`](../../ui/rendering/backend_isolation_plan.md)
- Sibling plan (perf): [`doc/03_plan/ui/perf/gui_web_2d_perf_fix_plan.md`](../../ui/perf/gui_web_2d_perf_fix_plan.md)

## Landed baseline (Phase 1 — verified anchors)

- **Single render funnel.** `shared_wm_scene_render_to_backend(backend: CompositorBackend,
  scene: SharedWmScene) -> SharedWmSceneRenderStats`
  (`src/lib/common/ui/window_scene_draw_ir.spl:443`) is the one executor for host WM
  and SimpleOS internal windows. It resolves background (`:445`), draws desktop chrome
  (`:446`), loops windows drawing chrome+content (`:448-454`), draws the taskbar (`:455`).
  Both lanes reach it through `shared_mdi_framebuffer_scene.spl:333,344`.
- **Chrome-kind.** `SharedWmWindow.chrome_kind` (`window_scene.spl:28`) is `"titled"`
  (`WM_CHROME_KIND_TITLED`, `:34`, default via `simple_gui_internal_window` `:125`) or
  `"borderless"` (`WM_CHROME_KIND_BORDERLESS`, `:35`). Executor gates the titlebar/border
  draw on it (`window_scene_draw_ir.spl:450`) and widens content to full window bounds for
  borderless (`_shared_wm_scene_window_content_rect:431-433`).
- **BackgroundSpec provider seam.** `BackgroundSpec` (`window_scene.spl:48`) = `kind: text`
  (`:49`), `color: u32` (`:50`), `source: text` (`:51`). `kind:"color"` implemented;
  `"image"`/`"motion"` are reserved names (struct comment `:43-47`). Single resolution point
  `shared_wm_scene_resolve_background` (`:71`): color → `resolved:true` (`:73`); unknown →
  `resolved:false` + `WM_BACKGROUND_UNRESOLVED_MARKER_COLOR` `0xFFFF00FF` (`:69,:76`) — loud,
  never a silent fill.
- **Persistent GPU sessions** (commit `a7b57550`): `Engine2dCompositorBackend`
  (`src/os/compositor/compositor_engine2d.spl:23`, `impl CompositorBackend` `:70`) wraps one
  persistent `Engine2D`; hosted-WM opt-in `SIMPLE_WM_RASTER=engine2d`
  (`src/os/hosted/hosted_entry.spl`). Raster-bound speedup **176x–684x** vs per-frame
  create+shutdown (commit `a7b57550`; `doc/00_llm_process/feature_expert/wm_gui_window_drawing/skill.md:300-307`).
- **Gates:** `check-engine2d-gpu-offload-evidence.shs`, `check-ui-backend-isolation.shs`,
  `check-hosted-wm-capture-evidence.shs`, `check-simpleos-wm-visible-display-evidence.shs`.

---

## A — BackgroundSpec image provider

**Motivation + evidence.** `BackgroundSpec.source` already exists as `text`
(`window_scene.spl:51`) and is written `""` by `shared_wm_background_color` (`:58`), but no
resolver consumes it: `shared_wm_scene_resolve_background` reads only `.kind`/`.color`
(`:71-76`), so `kind:"image"` currently returns the loud unresolved marker. This is the first
reserved provider to make real. A desktop wallpaper is the driving use case.

**Contract to design (author in the companion design doc, implement here):**
- **Source resolution.** `source` is a content reference resolved by a `BackgroundImageProvider`
  trait (design doc owns the signature). Host lane resolves a filesystem path via the
  `nogc_sync_mut` fs facade; SimpleOS/freestanding lane resolves only from an in-image
  pre-decoded surface (no `rt_file_exists`/theme-package reads on the baremetal lane — the
  boundary set in `shared_wm_renderer_unification.md:132-146`). The resolver returns decoded
  RGBA plus intrinsic w/h, never raw file bytes to the executor.
- **Scaling / letterbox policy.** One documented policy: scale-to-cover by default with a
  named `fit` field (`cover` | `contain` | `stretch` | `tile`), `contain` letterboxing to the
  desktop-chrome fill color. Executor draws the resolved surface via `backend.blit_pixels`
  (`display_backend.spl:17`); it must NOT introduce a per-pixel FFI loop (isolation/perf rule,
  `backend_isolation_plan.md` "Perf invariant"). Non-integer scale uses the existing
  `Engine2D.draw_image` path through `Engine2dCompositorBackend` (`compositor_engine2d.spl:100`),
  keeping resample math in the backend.
- **Caching (repo caching guard).** Cache decoded+scaled surfaces keyed by
  `(content_hash(source_bytes), target_w, target_h, fit)` — content-hash keying, matching the
  `WebRenderPixelArtifactCache` precedent (`web_render_pixel_backend.spl:111`). Cache lives on
  the compositor (host `content_caches` sibling on `host_compositor_entry.spl`), not on the
  pure-`common.ui` executor (executor stays stateless — it takes `scene`, returns stats).
- **Stale-serve semantics.** On a resolve error after a prior success (file removed, decode
  fails), serve the last-good cached surface AND surface a diagnostic; only when there is no
  prior good surface does the executor fall through to the loud `0xFFFF00FF` marker. This keeps
  the "loud on genuine failure, never silent default" contract while avoiding a wallpaper flash
  on a transient read error.

**Exact files.** `src/lib/common/ui/window_scene.spl` (extend
`shared_wm_scene_resolve_background` with an `"image"` branch + provider hook + resolution
struct fields for the decoded surface handle); `src/lib/common/ui/window_scene_draw_ir.spl`
(executor draws the resolved surface before chrome, at `:445-446`); host provider +
cache in `src/os/compositor/` (new small module `background_image_provider.spl`).

**Step list.** (1) Add `fit: text` to `BackgroundSpec` (default `"cover"`); update
`shared_wm_background_color` and every construction site (grep — the executor and
`shared_mdi_framebuffer_scene.spl`). (2) Extend `SharedWmBackgroundResolution` (`:60`) with an
optional decoded-surface handle + `stale: bool`. (3) Add the `"image"` branch to
`shared_wm_scene_resolve_background` calling an injected provider; keep loud marker for
no-provider / hard-fail. (4) Host `BackgroundImageProvider` impl + content-hash cache. (5)
Executor: blit the resolved surface (cover/contain/stretch/tile) before desktop chrome.

**Specs to add/extend.** New `test/01_unit/os/desktop/wm_background_image_provider_spec.spl`
(resolve color unchanged; image resolve returns surface; unknown kind still marker; stale-serve
returns last-good + diagnostic; cache hit on identical content-hash; each `fit` policy geometry).
Extend the existing background contract coverage in the executor spec set.

**Gates that must stay green.** `check-hosted-wm-capture-evidence.shs`,
`check-simpleos-wm-visible-display-evidence.shs` (must still validate readable title glyphs and
non-fake framebuffer — background must not mask chrome/text evidence),
`check-ui-backend-isolation.shs` (no new `rt_*`/backend construction in `common.ui`).

**Size:** M. **Dependencies:** none blocking (seam exists). **Risk + rollback:** wallpaper could
hide chrome/text evidence → mitigate by keeping the visible-display gate asserting glyphs on top
of the image; rollback = leave `kind:"image"` returning the loud marker (current behavior),
provider is additive.

---

## B — Motion / moving-image provider

**Motivation + evidence.** `kind:"motion"` is the second reserved provider name
(`window_scene.spl:43-47`); no frame-source abstraction exists yet. Depends on A landing the
surface-blit path first.

**Contract to design:**
- **Frame-source abstraction.** A `MotionBackgroundSource` yields the current frame surface for
  a wall-clock timestamp (`frame_for_time(t_micros) -> Surface`), advancing internally. Sources:
  looped decoded frame list (in-image, SimpleOS-safe) and, host-only, a live provider. The
  executor never decodes — it asks the source for "the frame now".
- **Cadence / dirty interaction with the present loop.** The WM present loop is dirty-gated
  (GUI-5a: present only on dirty, commit `a7b57550`). A motion background makes the desktop
  perpetually dirty, which would defeat that gate. Contract: the motion source exposes
  `next_frame_due_micros()`; the present loop treats "motion frame due" as a dirty trigger with
  its own cadence (default cap 30fps, configurable), independent of input dirtiness, and marks
  only the background region dirty (see item C region/dirty in the perf plan). Windows/chrome are
  NOT re-rastered when only the background frame advanced (they composite over a cached layer).
- **Perf budget.** Background frame advance + blit must fit the raster budget that keeps the WM
  composite off the critical path; target ≤ one `blit_pixels` of the desktop region per due
  frame, no per-pixel FFI, reuse the Engine2D persistent session
  (`compositor_engine2d.spl:23`). If the budget can't be met (large desktop, slow decode), the
  source must drop frames rather than stall the input path.

**Exact files.** `src/lib/common/ui/window_scene.spl` (`"motion"` branch + `MotionBackgroundSource`
trait), executor `window_scene_draw_ir.spl`, present-loop cadence in
`src/os/hosted/hosted_entry.spl` and the host compositor entry.

**Step list.** (1) Land A. (2) Define `MotionBackgroundSource` + `"motion"` resolver branch. (3)
Present loop: fold `next_frame_due_micros` into the dirty decision; region-mark background only.
(4) Frame-drop-under-budget policy + a wall-clock cadence cap.

**Specs to add/extend.** `wm_background_motion_spec.spl`: frame advances by wall-clock; dirty
trigger fires at cadence not per-input; windows not re-rastered on background-only advance;
frame-drop under an injected slow source; SimpleOS lane uses in-image frames only.

**Gates.** Same as A plus an idle-CPU non-regression note (motion must not push idle CPU back up
the way the pre-GUI-5a unconditional present did).

**Size:** L. **Dependencies:** A; region/dirty-rect work (perf plan next-wave) makes the
background-only invalidation efficient — without it, motion re-rasters the whole desktop.
**Risk + rollback:** perpetual-dirty regressing idle CPU; rollback = `kind:"motion"` returns the
loud marker.

---

## C — Borderless adoption for the taskbar dock

**Motivation + evidence.** The taskbar is drawn by `shared_wm_scene_render_taskbar`
(`window_scene_draw_ir.spl:359`): it fills a dock rect (`:367`) and loops items (`:368-378`,
item-x `:371`, item fill `:377`), using the pure-math geometry helpers `wm_taskbar_item_width`
(`:262`), `wm_taskbar_dock_width` (`:269`), `wm_taskbar_item_x` (`:274`). It is a bespoke draw
block, NOT a `SharedWmWindow`. Now that `chrome_kind:"borderless"` exists
(`window_scene.spl:35`) — a titlebar-less full-content window — the dock is the natural first
borderless-window adopter, which would collapse the special-case taskbar path into the generic
window loop and prove the borderless path end-to-end.

**Design to author.** Model the dock as a borderless internal window (or a borderless
"drawn object" window) whose content renderer paints the item buttons. Decide:
- **Hit-test / z-order.** The dock window pins to a reserved z-band above app windows and below
  any modal chrome; taskbar hit-testing (`wm_lifecycle_hit_taskbar`, cited in
  `shared_wm_renderer_unification.md:126`) must continue to resolve item indices — so the
  borderless dock window must expose the same item geometry (reuse `wm_taskbar_item_x` for
  hit-test, do not fork it). Focus never transfers to the dock (it is chrome, not an app).
- **Content painter.** Reuse the existing item-loop draw as the dock window's borderless content
  renderer so pixels are byte-identical to today (this is a refactor, not a visual change).

**Exact files.** `src/lib/common/ui/window_scene_draw_ir.spl` (convert the taskbar block to a
borderless-window render, or have the window loop emit it), `window_scene.spl` (a dock-window
constructor if needed), hit-test callers (`wm_action_applier.spl` re-exports, per impl spec
`:49-51`).

**Step list.** (1) Add a borderless dock window to the scene the executor builds (or wrap the
existing taskbar block behind the borderless-window path). (2) Route hit-test through the same
geometry helpers. (3) Assert byte-identical pixels vs the current taskbar (capture before/after).

**Specs.** Extend `check-wm-multiapp-taskbar-evidence.shs` expectations (taskbar focus/minimize/
restore, readable title text, close-button pixels stay green); add a pixel-identity assertion
dock-as-window vs legacy block.

**Gates.** `check-wm-multiapp-taskbar-evidence.shs`, `check-hosted-wm-capture-evidence.shs`.

**Size:** M. **Dependencies:** none (borderless path landed). **Risk + rollback:** hit-test/z-order
regression → mitigate with the pixel-identity + taskbar-interaction gate; rollback = keep the
bespoke `shared_wm_scene_render_taskbar` block (leave it unchanged). Treat this item as OPTIONAL
("if natural") — do not force it if the pixel-identity constraint proves costly.

---

## D — SimpleOS visual-proof dependency (BLOCKING)

**Motivation + evidence.** The SimpleOS x86_64 GUI lane cannot serve as end-to-end visual proof
for the providers above until the freestanding module-init / primitive-global fault is fixed.
Recorded evidence:
- `doc/08_tracking/bug/freestanding_wrapper_profile_i32_global_var_shifted_2026-07-02.md` (P2,
  **OPEN**): in the Cranelift `--entry-closure` freestanding profile, a primitive non-heap module
  global reads garbage before assignment and a stored immediate is shifted `>>3`
  (`g_win0_w=128` after `g_win0_w = 1024`; also `768 -> 96`). Names `gui_entry_engine2d.spl` as
  the affected lane; reproduces on HEAD.
- Memory `project_simpleos_gui_boot_2026-05-28.md`: root cause is `__simple_call_module_inits`
  being undefined-weak and never called in the freestanding path — (1) `linker.rs`
  `read_global_symbols` strips a leading `_` gated on the *host* being macOS, so cross-compiled
  ELF `__module_init_*` symbols become `_module_init_*` and miss the `starts_with("__module_init_")`
  match; (2) `link_objects_freestanding` (linker.rs:1027) has no wrapper that calls
  `__simple_call_module_inits` before entry.
- Entry file: `examples/09_embedded/simple_os/arch/x86_64/gui_entry_engine2d.spl` (its header
  `:36-45` documents avoiding module `var` globals precisely because of this bug, and uses the
  freestanding Engine2D core rather than the full facade).

> Anchor correction: the brief's "FAULT @0x277d09" address is **not recorded anywhere in this
> repo or the memory dir** — the recorded symptom is the `>>3` primitive-global shift + garbage
> pre-init above, not a fault at that address. Cite the bug/memory records, not the address.

**Fix directions (from the records — this item tracks the fix, does not re-diagnose).**
1. Gate the leading-`_` strip in `read_global_symbols` on the **target** object format being
   mach-o, not the host OS, so cross-compiled ELF `__module_init_*` symbols match and the
   aggregator `__simple_call_module_inits` is generated.
2. Ensure the freestanding link (`link_objects_freestanding`, linker.rs:1027) / `crt0.s`
   (`examples/.../boot/crt0.s`) calls `__simple_call_module_inits` before `spl_start`.
3. Fix the primitive-global store lowering: diff freestanding vs normal Cranelift lowering for a
   plain-immediate store into a primitive module global (the spurious `>>3` tag-untag). Cross-check
   `llvm_backend_missing_module_init_heap_globals_2026-06-15` and
   `native_object_cache_key_omits_seed_version_2026-06-15`.

These are **Rust seed / Cranelift lowering + linker** changes — off the pure-Simple default path,
owned by the bootstrap/backend maintainer, not this UI wave. This item's job is to (a) mark it as
the blocker on SimpleOS visual proof for A/B, and (b) hand the fix directions to that owner.

**Exact files (for the seed owner).** `src/compiler_rust/.../linker.rs`
(`read_global_symbols`, `link_objects_freestanding:1027`), the freestanding entry-closure lowering,
`examples/09_embedded/simple_os/arch/x86_64/boot/crt0.s`.

**Acceptance.** `check-simpleos-wm-visible-display-evidence.shs` passes with real module globals
(not the current locals/params workaround), and `g_win0_w` reads `1024` not `128`.

**Size:** L (seed). **Dependencies:** none, but blocks the SimpleOS half of A/B visual proof.
**Risk + rollback:** until fixed, host lane is the visual-proof vehicle for A/B; SimpleOS proof
stays on the current worked-around chrome/text evidence. Do NOT convert the bug record to a NOTE
and do NOT remove the workaround comment in `gui_entry_engine2d.spl` until the fix lands.

---

## E — fb-lane trait unification remainder (CompositorBackend vs RenderBackend)

**What the executor landing already resolved.** The scene renderer
`shared_wm_scene_render_to_backend` (`window_scene_draw_ir.spl:443`) is written **only** against
the backend-neutral `CompositorBackend` trait (`display_backend.spl:9-20`). Both host-WM
capture and SimpleOS QEMU lanes render through this one consumer API
(`shared_mdi_framebuffer_scene.spl:333,344`). The *consumer* side is unified — no lane keeps a
separate window renderer.

**What remains.** Two distinct trait definitions still coexist:
- `CompositorBackend` (`display_backend.spl:9-20`): coarse chrome/blit vocabulary — `clear`,
  `fill_rect`, `draw_text`, `draw_char_8x16`, `put_pixel`, `blit_pixels`, `present`,
  `present_rect`, `as_glass_capable`.
- `RenderBackend` (`src/lib/gc_async_mut/gpu/engine2d/backend.spl:57-80`): richer primitive +
  readback + clip/mask vocabulary — `draw_rect_filled`, `draw_line`, `draw_circle`,
  `draw_gradient_rect`, `draw_image`, `set_clip`/`set_mask`, `read_pixels`,
  `read_pixels_with_source`, etc.

They are joined only by concrete adapters (`Engine2dCompositorBackend` implements
`CompositorBackend` by delegating into an `Engine2D` that owns a `RenderBackend`,
`compositor_engine2d.spl:70-104`; `GpuCompositorBackend` bridges `VirtioGpuDriver`,
`display_backend.spl:29`). There is no trait-to-trait adapter and no blanket `impl`.

**Design decision to author (in the design doc), then execute.** Pick ONE:
1. **Keep two traits, formalize the bridge (recommended, low risk).** Document
   `CompositorBackend` as the compositor/present surface and `RenderBackend` as the primitive
   draw surface; keep `Engine2dCompositorBackend` as the sanctioned adapter; add the missing
   `present_rect`-honoring readback method the perf plan's dirty-tile item needs, on
   `CompositorBackend`. No trait merge.
2. **Unify onto one trait** — high risk, touches every backend impl; only if a concrete need
   (e.g. the executor needing `read_pixels`/clip that `CompositorBackend` lacks) forces it.

The executor today needs only the coarse vocabulary, so option 1 is the default. The one concrete
gap that could force more is region readback (`read_pixels_region`) for dirty-rect present, which
lands on `CompositorBackend`/`present_rect` — see the perf plan next-wave item.

**Exact files.** `display_backend.spl` (any added method), `compositor_engine2d.spl` (adapter),
design doc.

**Specs.** No new pixel spec (structural); assert `Engine2dCompositorBackend` still satisfies
`CompositorBackend` after any method addition (compile gate) and the offload contract spec stays
green (`engine2d_gpu_offload_contract_spec`, 11/11 per commit `a7b57550`).

**Gates.** `check-engine2d-gpu-offload-evidence.shs`, `check-ui-backend-isolation.shs`.

**Size:** S (option 1) / L (option 2). **Dependencies:** the dirty-tile readback item (perf plan)
is the thing most likely to add a method here. **Risk + rollback:** option 2 could destabilize
every backend; default to option 1 and only escalate on a proven need. Rollback = document-only
(the traits already work as-is).

---

## Dispatch / sequencing

| Item | Size | Blocks / blocked-by | Lane |
|---|---|---|---|
| A image provider | M | — | UI (pure-Simple) |
| B motion provider | L | needs A + region-dirty (perf plan) | UI |
| C borderless taskbar | M | optional; borderless landed | UI |
| D SimpleOS module-init fix | L | blocks SimpleOS proof of A/B | **seed owner** |
| E trait remainder | S/L | E option-2 may be forced by dirty-tile readback | UI |

Recommended order: A → C (independent) → E(option 1) → B (after region-dirty) ; D runs in
parallel on the seed owner's track and gates only the SimpleOS visual-proof column, not host-lane
delivery of A/B/C.
