# WM Window-Render API Hardening — Phase 2 Plan

**Status:** DRAFT (2026-07-07) · updated 2026-07-14 — see [§D.1](#d1--2026-07-14-status-update-full-desktop-native-build-lane):
full-desktop `gui_entry_desktop` native build perf SOLVED (~87 s) and the hardened lane BOOTS
+ `first-frame-rendered`; real screendump now gated only on a rust-seed cross-module
field-index-misresolution fix (in flight). · **Owner:** OS/desktop + UI/rendering · **Scope:** the
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

**Status: LANDED 2026-07-07 (PPM decode only; PNG deferred).** Implemented as
designed below: `BackgroundImageProvider` trait on `window_scene.spl`, host
provider + content-hash cache + stale-serve in the new
`src/os/compositor/background_image_provider.spl`, registered via
`shared_wm_scene_register_background_image_provider` in `init_host_wm`
(`host_compositor_entry.spl`). Decodes PPM (P6) via
`src/lib/common/image/ppm_decode.spl`; PNG decode is NOT implemented (out of
scope for this landing — track separately if wallpaper assets need PNG).
`fit` supports `cover`/`contain`/`stretch`/`tile`. SimpleOS/freestanding has
no registered provider yet (loud marker on `kind:"image"` there, matching the
documented no-provider contract). See feature-expert skill
`doc/00_llm_process/feature_expert/wm_gui_window_drawing/skill.md` for gate
coverage and the two interpreter bugs found during this work. Dead
`MotionBackgroundSource` trait (unused scaffolding, zero implementers) was
deleted during review; item B below is unaffected (still open, no contract
landed).

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

**Status (fix-round, 2026-07-07): I8 staged-deferred.**

*Landed:*
- `MotionBackgroundSource` trait + `"motion"` resolver branch
  (`src/lib/common/ui/window_scene.spl`), fs-backed `HostMotionBackgroundSource`
  (`src/os/compositor/background_motion_provider.spl`), executor threading of
  `t_micros` (`window_scene_draw_ir.spl`, `shared_mdi_framebuffer_scene.spl`).
- `next_frame_due_micros()` dirty-trigger fold + the pure
  `shared_wm_motion_dirty_due` predicate, plus a self-re-arming present-loop
  seam (`hosted_entry.spl`, `shared_wm_motion_background_consume_due`) that
  advances next-due itself instead of depending on render-side consumption.
- **The shared-MDI production lane animates with real time threading**:
  `render_shared_mdi_framebuffer_scene_for_windows` /
  `_for_simple_gui_scene` (`shared_mdi_framebuffer_scene.spl`) now forward a
  caller-supplied `t_micros` all the way to the resolver — a registered
  motion source genuinely advances frames through this real production
  entry point, not only through direct `SharedWmScene` construction in
  tests.
- Not-yet-scheduled `-1` sentinel (was `0`, which caused a spurious dirty
  fire at process start before any frame had ever been selected) plus
  registration-time seeding of the real first due
  (`ensure_host_motion_background_source_registered`).
- Specced end-to-end in `wm_background_motion_provider_spec.spl` (10
  examples): construction loud-fail matrix, pure time-based frame advance +
  frame-drop, dirty-trigger once-per-due-value + self-re-arm across
  intervals, single-frame static degrade, image-cache reuse, resolve-time
  loud-fail (no source / unreadable frame, no stale-serve), production-lane
  animation via the real wrapper call chain, and the sentinel regression
  guard.

*Deferred at the 2026-07-07 fix-round checkpoint (see follow-up 1/2 below for
what has since landed):*
- **SimpleOS lane** has no motion wiring — tracked under item D (SimpleOS
  visual-proof lane is blocked independently by the freestanding
  module-init/primitive-global fault, see the design doc's Lane-parity
  section).
- **Video/codec sources are out of scope**, not deferred — the design
  explicitly restricts motion sources to an ordered PPM frame list; decoding
  a real video container was never part of this item's contract.

**Status update (2026-07-07, follow-up 1+2 LANDED):**

1. **I8 region-dirty — LANDED.** `HostCompositor.render_background_only(t_micros)
   -> bool` (`host_compositor_entry.spl`) presents a due background advance
   without re-rastering windows/chrome: `host_background_visible_rects`
   computes the desktop rect minus the union of every visible (non-minimized)
   window rect via axis-aligned rectangle subtraction
   (`_host_rect_subtract_one`, 0-4 pieces per window), returning
   `HostBackgroundRegion{rects, computed}`; `computed:false` (a rect-count
   safety cap, `HOST_BACKGROUND_REGION_DIRTY_MAX_RECTS=256`) is the
   correctness escape hatch — `render_background_only` returns `false` and
   the caller falls back to a full `render_frame()` rather than risking an
   incorrect partial paint on a pathological window layout. Only the
   background-visible sub-rects are touched (`blit_pixels`/`fill_rect` per
   rect, cropped from the resolved `BackgroundSurface` by
   `host_background_crop_surface`), so window/chrome pixels drawn by the
   prior full render are left byte-exact — proven by a spec that samples a
   window-body pixel across two background-only advances
   (`wm_background_motion_hosted_consumption_spec.spl`). `hosted_entry.spl`'s
   present loop now tracks `other_dirty` (input/warmup — forces the existing
   full path) separately from `motion_dirty` (background-only trigger only —
   takes `render_background_only`, falling back to `render_frame()` on a
   `false` return).
2. **Hosted-lane consumption — LANDED.** `HostCompositor` gained a
   `background: BackgroundSpec` field (default: a plain color matching the
   historical hardcoded `theme.compositor_bg` fill) + `set_background(spec)`
   + `_resolve_background(theme, t_micros)`, which re-reads the LIVE
   `theme.compositor_bg` for `kind:"color"` (so a runtime theme change stays
   honored exactly as before this field existed) and passes `kind:"image"`/
   `"motion"` straight to `shared_wm_scene_resolve_background` — the SAME
   resolver the shared-MDI production lane already uses.
   `render_frame()`'s direct-draw fallback lane calls `_resolve_background`
   before `shared_wm_scene_render_desktop_chrome` instead of hardcoding
   `theme.compositor_bg`; the fast CSS/GUI-web lane's gate now additionally
   requires `self.background.kind == WM_BACKGROUND_KIND_COLOR` (that lane
   rasterizes one opaque flat-color backdrop with no image/motion
   compositing seam, so `kind:"image"`/`"motion"` always routes through the
   direct-draw lane instead — the fast lane is otherwise untouched and stays
   byte-identical for the default/unset-motion case, confirmed by
   `engine2d_gpu_offload_contract_spec.spl`'s exact-pixel assertion).
   `ensure_host_motion_background_source_registered` (env-gated on
   `SIMPLE_WM_MOTION_MANIFEST`) now also latches the manifest/fit on success
   (`_host_motion_background_manifest_ok`/`_fit_ok`) via
   `host_motion_background_registered_spec()`, and `init_host_wm` calls
   `comp.set_background(...)` with it — so the SAME manifest that registers
   the process-wide `MotionBackgroundSource` also becomes the compositor's
   resolvable `BackgroundSpec`, with the unset-env lane staying byte-identical
   (kind stays `"color"`, nothing new is reachable).
   New spec: `test/01_unit/os/desktop/wm_background_motion_hosted_consumption_spec.spl`
   (6 examples) — two absolute-time samples through `render_background_only`
   resolve different frames; a background-only advance leaves a window-body
   pixel untouched across two frame advances (I8); an unregistered motion
   source paints the loud `WM_BACKGROUND_UNRESOLVED_MARKER_COLOR` at the
   hosted-consumption layer (never a silent stale/default); `render_frame()`'s
   direct-draw lane resolves a configured (single-frame, deterministic)
   motion background; plus 2 pure rectangle-math examples for
   `host_background_visible_rects`.
3. **PNG/video sources** — still explicitly future/optional, not committed:
   if ever pursued, requires a new `MotionBackgroundSource` implementation
   (e.g., video-decode-backed) behind the same trait; the manifest/PPM-list
   source stays the baseline, host-only implementation.

Item B is now complete per follow-up (1) and (2); only follow-up (3)
(PNG/video, optional/future) and the SimpleOS lane (item D dependency)
remain open.

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

### D.1 — 2026-07-14 status update (full-desktop native-build lane)

The visual-proof target moved from the single-window `gui_entry_engine2d.spl` (item D above)
to the **full desktop** `gui_entry_desktop.spl` (created 2026-07-11: launcher + 15 apps +
taskbar + `SharedWmScene`/`TaskbarModel`/`FramebufferDriver` graph, native 3840×2160). Status:

**Solved — build perf (was mis-blamed on "lexer O(n²)").** The multi-hour SimpleOS GUI kernel
build was the gate selecting the **aarch64 self-hosted compiler run under qemu-user emulation**
(`bin/release/*/simple` glob picks aarch64 alphabetically) — ~1500× slower (>100s / 200 lines).
Building with the **native x86 compiler** (`bin/release/x86_64-unknown-linux-gnu/simple`, rust
seed) + gate env (`SIMPLE_BOOTSTRAP=1 SIMPLE_LIB=$PWD/src SIMPLE_ALLOW_FREESTANDING_STUBS=1`,
llvm-objcopy on PATH) builds the whole kernel in **~87 s**. Native lint is O(n) (8000 lines /
0.077 s) — there is no lexer quadratic in the deployed compiler. Full recipe: session scratchpad
`screendump_repro.md`.

**Proven — the hardened lane boots.** The 87 s native kernel boots under QEMU (q35/max/2G,
`-vga std -global VGA.vgamem_mb=64`, nvme FAT32 font disk) to: `engine2d-ready
backend=baremetal-framebuffer → compositor ready → shell initialized → 15 apps → [wm-frame]
executor → first-frame-rendered`. So the phase-1/phase-2 hardened Engine2D/compositor/shell
lane executes on real SimpleOS.

**Remaining blocker (NEW, deeper than item D's primitive-global shift) — rust-seed cross-module
FIELD-INDEX misresolution.** Screendump is black + `cr2=0x0` nil-receiver panic cascade
("field access on nil receiver"). Root cause (team-confirmed):
`src/compiler_rust/compiler/src/hir/lower/type_resolver.rs:155` registers imported struct fields
as `TypeId::ANY`, so nested field chains yield ANY receivers; for an ANY receiver the field
INDEX is resolved by a receiver-BLIND "struct with the MOST fields declaring this name wins"
scan (`type_resolver.rs:548-564`/`:599-625`; `expr/access.rs:337-346` keeps the wrong index,
only degrading the TYPE to ANY). With 57 structs declaring `background`, 801 `width` at
differing indices, the scan picks the wrong struct → one-slot shift → nil → panic. First victim:
`scene.background` (SharedWmScene field after the `windows:[]` array) in `_wm_draw_ir_desktop_batch`.
CONFIRMED source-UNworkaroundable at the field level: reordering fields only MOVES the victim
(background→windows). Full-graph-only (isolated 2-module repro reads correctly). The `.spl`
`resolve_field_index` is DEAD CODE here (MIR consumes a pre-resolved HIR `field_index`) — the fix
is RUST-seed only. This is NOT a regression: the Jul-6 1024×768 proof (`wm_shared_evidence/
fullscreen.ppm`) was the smaller `gui_entry_engine2d.spl`, whose closure lacked the collisions.
Bug record: `doc/08_tracking/bug/simpleos_native_build_framebufferdriver_crossmodule_field_offset_shift_2026-07-14.md`.

**Fix (in flight).** Make ambiguous-field resolution use the receiver's REAL struct
(`access.rs try_resolve_receiver_struct_name_from_expr` → `try_resolve_global_field_index_by_name`)
instead of most-fields-wins, and extend the `AmbiguousFieldNames` computation (over
`imports.struct_defs` today) to also flag index-disagreements in local `module.types`. Requires a
cargo seed rebuild (~2–6 min incremental, no parallel cargo) + the 3-stage byte-identical bootstrap
gate + this PPM gate — all runnable on this Linux host (the prior attempt was blocked on a
broken-native-build Mac). Fallback stopgap: extend the existing `fb_w/fb_h` scalar-threading /
nil-guard workaround to the `SharedWmScene`/`TaskbarModel` fields the composition reads, for a
non-black PPM before the compiler fix lands.

**Render-lane confirmation (same day):** guarding the composition's `scene.background` derefs +
bypassing the internally-faulting font-metrics call makes the composition BUILD FULLY and reach
`first-frame-rendered`; the paint step then returns `rendered=0` because the Engine2D CPU
rasterizer reads shifted `FramebufferDriver.width/height` at creation
(`src/lib/gc_async_mut/gpu/engine2d/backend_baremetal.spl:59-60`). So the ENTIRE render chain is
the SAME field-shift root cause — the ready compiler patch fixes composition + Engine2D dims in
one shot; the `fb_w/fb_h` workaround on main only covered host-gpu present dims. The remaining
independent blocker is a separate HEAD-seed NVMe-init regression that must be fixed to build a
HEAD-seed kernel that boots to the render stage (to verify the field fix). Render-lane bisect:
`scratchpad/render_findings.md`; patches: `scratchpad/screendump_handoff/`.

**Acceptance (D.1).** `check-simpleos-wm-fullscreen-evidence.shs` captures a non-black
(>1%) 3840×2160 PPM of `gui_entry_desktop`, AND the seed still passes the 3-stage bootstrap gate.

**Owner.** Rust-seed HIR-lowering maintainer (same as item D's linker/lowering owner). This UI
wave supplies the fast native-build repro loop + the confirmed root cause; it does not own the seed fix.

### D.2 — 2026-07-16 status (full landed fix chain)

**Landed today — interconnected struct-lowering + Result routing corrections:**
- `7a4cb1ab3d3` + `81fe38e6dd6`: seed spl_arg providers (plain cargo builds fixed)
- `86e56ca7867`: qualified Result.Ok/Err routing (NVMe init_from_grant root)
- `610b4572a32`: bootstrap rewrite was deleting Try operators (BinaryWriter.len root)
- `77c519cdab43`: trait-impl virtualization scoped to local impls (fb-init regression)
- `73b6b02eca2`: BGA enable-bit fix, rt_file_read_bytes weak + VFS export, font soft-fail, frame-degraded policy
- `4c1a5365c61`: unconditional rasterizer clipping, per-command preflight, strong dl stubs, Engine2D nil pinning
- `6b59a8c4bf7`: struct-init declared-order lowering (Symptom A root fix)
- `8932fcb3a14`: vtable NAME-keyed (Symptom B root fix; all 13 RenderBackend vtables)

**Boot depth:** compositor ready → shell initialized → launcher apps=15 → [wm-frame] executor → first-frame-rendered

**Screendump state:** 3840×2160 honest dims (QMP `-vga std`, real OVMF + nvme FAT32), still **BLACK** (0.00%);
confirmed as downstream of cross-module field-index shift (access.rs patch ready but uncommitted)

**Open blocker:** compose retry-recovery leak — alloc sz 8MB per `create_offscreen` → ~5 faults exhausts heap → boot halts.

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
| A image provider | M | — | UI (pure-Simple) — **LANDED 2026-07-07 (PPM only)** |
| B motion provider | L | needs A + region-dirty (perf plan) | UI |
| C borderless taskbar | M | optional; borderless landed | UI |
| D SimpleOS module-init fix | L | blocks SimpleOS proof of A/B | **seed owner** |
| E trait remainder | S/L | E option-2 may be forced by dirty-tile readback | UI |

Recommended order: A → C (independent) → E(option 1) → B (after region-dirty) ; D runs in
parallel on the seed owner's track and gates only the SimpleOS visual-proof column, not host-lane
delivery of A/B/C.
