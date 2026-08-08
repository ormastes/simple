# Unified 2D Event + Panel + GPU Offload — Architecture Revision (2026-07-30)

Supersedes nothing; extends `unified_2d_interaction_2026-07-20.md` with the
survey findings below and commits the missing bridges. Companion review:
`web_wm_gpu_3d_review_2026-07-20.md`.

**2026-07-31 reconciliation:** current status and remaining work are governed by
`draw_ir_web_renderer_reconciliation_2026-07-31.md`. D1 pointer-down dispatch is
complete but wheel dispatch is open; D2 producer parent metadata is partial;
D9 batching must be read per backend, not as universal completion.

## Survey findings (5-lane research, 2026-07-30)

1. **Interaction core is DONE but orphaned.** `src/lib/common/engine/interaction/`
   (pointer_event, event_route, hit_proxy, hit_test, pointer_capture) is complete,
   DOM-semantics (capture→target→bubble, stop/immediate/prevent, once, pointer
   capture), and green: `interaction_core_spec.spl` 15/15,
   `event_backend_matrix_spec.spl` 8/8. Zero production importers.
2. **DrawIR is a flat batch model.** `DrawIrComposition → [DrawIrBatch] →
   [DrawIrCommand]`. `parent_id` exists (`draw_ir.spl:84`) but only the drawio
   bridge reads it; `hit_rect` (`draw_ir.spl:80`) is populated but has zero
   consumers; event targeting is string-id match (`draw_ir_event_target_context`,
   `draw_ir.spl:596`) — it cannot answer "what is under this pixel".
3. **Four disjoint event vocabularies, no converters:** `WindowEventRecord`
   (contract ring, test-injected only), compositor `KeyEvent`/`MouseEvent`
   (winit path), `UIEvent` (TUI/web reducer `common/ui/event.spl:45`),
   `PointerEvent2D` (unused core). WM/taskbar dispatch hardcodes rect tests in
   `window_scene.spl:819-944` returning action strings. `WINDOW_EVENT_WHEEL` has
   no consumer. `window_winit_input_event.spl` is a dead struct.
4. **Three scroll implementations, all orphaned or benchmark-only:**
   `common/ui/scroll_surface.spl` (only caller: an example),
   `*/compositor/scroll.spl` (×3 tier copies, zero callers),
   `event.spl handle_scroll`. No momentum anywhere.
5. **GPU lane is drawing-only by construction.** One packet kind
   (`KIND_DRAW_IR`), lane scheduler rejects `per_widget_dispatch` and
   `mutates_host_semantics` (`backend_lane.spl:167-172`), readback is
   pixels+checksum only (`Engine2DReadback`). No GPU hit-test/collision kernel
   exists. Draw kernels (fill/rect/circle/line/triangle/gradient/blit/glyph
   composite) are proven via parity + live specs for CPU/Vulkan/CUDA.
6. **Fonts have a real hub** — `text_layout/font_renderer.spl` (measure/shape/
   atlas, skia shaper, GlyphCache) feeding `draw_ir_target.draw_text*` — but
   three vector rasterizers exist (stb_truetype C production path, pure-Simple
   `common/encoding/sfnt_glyf.spl` orphaned, `font_vector_data.spl` toy) and the
   bitmap path is 5x7/8x16 ASCII only. GPU font work = atlas composite;
   glyph raster offload is env-var-simulated.
7. **Duplication debt (measured):** 1,714 relative paths duplicated across lib
   tiers, 3,391 extra copies; sampled copies have DRIFTED (web_ui/event_bus ×4
   copies = 4 distinct hashes; replay/event_log ×4 = 4 hashes). The
   nogc engine2d mirror is partial and divergent (111 diff entries; no
   compositor/session there at all).
8. **Perf baseline (measured 2026-07-30):** `hit_stack` over 2,000 proxies with
   a ~776-deep ancestor chain = **189µs/call** (self-hosted `bin/simple run`).
   Insertion sort in `hit_test.spl` is O(n²) on *candidates at a point* (small
   N) — acceptable by design. CPU dispatch is not the bottleneck at input rates;
   no perf gate blocks adoption of the core.

## Decisions

- **D1 — One event core.** `common/engine/interaction` is the only 2D event
  router. `window_scene` rect tests, `draw_ir_event_target_context` string
  matching, and per-app drag tracking migrate onto it. `common/ui/event.spl`
  stays as the app-level reducer but is FED BY dispatch outcomes, not raw input.
- **D2 — DrawIR is the hit source.** New bridge `common/engine/interaction/
  draw_ir_hit_bridge.spl`: `DrawIrComposition → ([HitProxy2D], Dict<i64,i64>)`.
  Batch = group node (embedding x/y/w/h/layer/clip → proxy + render_layer);
  command with `hit_rect` = leaf; `component_id`/`parent_id` hashed to stable
  i64 node ids. This makes `hit_rect` and `parent_id` load-bearing for the
  first time. Producers (WM, widget_draw_ir, web renderer) must populate
  `parent_id` going forward.
- **D3 — Panel2D.** One panel abstraction (`common/ui/panel2d.spl`) = DrawIR
  group + HitProxy + optional scroll model + `opacity_milli` + layer. Used by:
  internal windows (`simple_gui_internal_window`), taskbar, in-game HUD
  objects. Pointer transparency is `PointerPolicy`, never pixel alpha (already
  the core's rule). Scroll consolidates on `scroll_surface.spl` (`ScrollModel`)
  wired to wheel events; the 3 orphaned `compositor/scroll.spl` copies are
  deleted when Panel2D lands.
- **D4 — Input transport.** `HostedInputBackend` (winit) enqueues
  `WindowEventRecord`s; `window_winit_input_event.spl` becomes the real
  bridge; one adapter `WindowEventRecord → PointerEvent2D`. Wheel gets a
  dispatch branch.
- **D5 — Collision = same proxies.** Group collision detect is AABB overlap
  over the same HitProxy2D forest (pairwise within a group set; uniform-grid
  broadphase only when a measured workload needs it). Physics contact events
  reuse `EventListener2D` kinds — one listener registry for pointer AND
  collision.
- **D6 — GPU offload is staged, board-runnable rule applies.**
  - Stage A (CPU-authoritative, GPU-verified): new packet kind `KIND_HIT_QUERY`
    in `host_gpu_event_queue`, batch-op exemption in
    `_engine2d_host_gpu_is_batch_operation`, and a scalar readback channel
    beside `Engine2DReadback` — the three pieces the queue lacks today.
  - Stage B: vulkan/cuda ID-buffer kernel (`simple_2d_hit_grid_u32`): rasterize
    node-ids into a u32 grid alongside paint; hit query = one texel read;
    event forward = host builds PointerEvent2D from GPU-resolved node id.
    CPU software backend implements the same kernel for parity (existing
    parity-spec pattern).
  - Full 2D processing offload continues on the existing proven kernel surface;
    events remain host-authoritative (per `gpu_full_render_offload_mdsoc_plus_
    plan.md`) with the GPU as the hit-resolution accelerator.
- **D7 — Fonts.** `FontRenderer` hub is the single API for panels/game/web.
  Bitmap tier: keep 5x7/8x16 for baremetal/cheap panels. Vector tier:
  stb path stays production; pure-Simple `sfnt_glyf` is the long-term canonical
  parser (Pure Simple First) — new consumers target the hub, never a rasterizer
  directly. No fourth rasterizer, ever.
- **D8 — Dedup rules (hard).** All new 2D event/panel code lives ONLY in
  `common/` — no tier mirrors. Any touched drifted tier-copy is consolidated or
  deleted in the same change. engine2d nogc mirror gets no new files from this
  campaign.

- **D9 — IR pipeline optimization contract (audit 2026-07-30).** Layering is
  confirmed: GUI widgets and the web renderer both emit `DrawIrComposition`
  DIRECTLY (no WebIR/GuiIR exists; `widget_draw_cmds.spl` is a dead second GUI
  IR — delete it). The contract:
  - **DrawIR → backend remains the worst hop, but status is backend-specific.**
    Vulkan shares submissions across compatible buffered primitives, but
    image/transition operations flush and per-primitive dispatch remains. CUDA
    and Metal expose `RenderBackend.submit_batch` but their implementations are
    no-ops and CUDA still synchronizes per operation.
    Required: packed rect/kind instances, persistent descriptors/buffers,
    reduced dispatches, and a device-side glass pass. The current full-frame
    readback/host-crop seam is not device-region readback.
  - **Producers minimize conversion and copies:** `widget_draw_ir.spl`
    copy-in/copy-out on value-type arrays is O(N²) per frame → pass `mut cmds`;
    web path stops prepending the canvas command (O(N) rebuild at
    `simple_web_html_layout_renderer.spl:1059`) and stops re-formatting
    `component_id` strings per node per frame (cache on layout node).
  - **Big-object allocation:** compositions/batches get capacity-preallocated
    command arrays (big-block alloc up front, no push-grow), and the frame path
    adopts the already-built-but-unused `draw_ir_diff`/`draw_ir_patch` so a
    retained composition is patched, not rebuilt from scratch each frame.

## Phasing (maps to campaign lanes)

| Lane | Delivers | Depends |
|---|---|---|
| L1 bridge | D2 + D5 (draw_ir_hit_bridge + collision) + specs | — |
| L2 panel | D3 Panel2D (internal window/taskbar/scroll/transparent/layers) + specs | L1 |
| L3 input | D4 transport + wheel + WM dispatch migration + hardening specs | L1 |
| L4 gpu | D6 stage A then B, vulkan+cuda+software parity | L1 |
| L5 font | D7 hub wiring for Panel2D text, bitmap+vector spec | L2 |
| L6 ir-cpu | D9 producer fixes: mut cmds, no prepend, id cache, prealloc, dead-IR delete | — |
| L7 ir-gpu | D9 `submit_batch` frame encoding: Vulkan first, then CUDA; parity spec stays green | L6 |

## Lane results (verified 2026-07-30, every line re-run by the coordinator)

| Lane | Spec | Result |
|---|---|---|
| core | `interaction_core_spec` | 15/15 |
| L1 bridge | `draw_ir_hit_bridge_spec` | 10/10 |
| L3 input | `window_event_adapter_spec` | 9/9 |
| L2 panel | `panel2d_spec` | 13/13 |
| L5 font | `panel2d_text_spec` | 7/7 |
| L4 gpu (Stage A) | `host_gpu_hit_query_spec` | 7/7 |
| Red 1 | `..._module_split_spec` | 2/2 (147,122 B split 43,036 + 104,342; fn count 24 → 24) |

**D9 CORRECTION — the survey text above was partly stale.** Commit `de1b31027d7`
(2026-07-29, "perf(vulkan): batch Engine2D primitive dispatches") had ALREADY
landed per-frame descriptor-set reuse and single-fence flush
(`frame_batching_enabled`, `_enqueue_framebuffer_compute`,
`_flush_pending_compute`) for the three main Vulkan creation paths. The D9 claim
of per-command fences was written the next day without accounting for it.
What L7 actually added: trait-level `RenderBackend.submit_batch()`, the two
creation paths that had missed `enable_frame_batching()` (directx-on-vulkan,
metal-on-vulkan), and an unconditional whole-frame flush in `draw_ir_adv.spl`
— closing a latent gap where a readback-only path could read unflushed state.

Still NOT done from D9, explicitly:
- SSBO instance-buffer packing (still one `vkCmdDispatch` per primitive) and
  explicit staging-buffer reuse — needs new SPIR-V/GLSL kernel work, unsafe to
  validate with no Vulkan hardware present.
- Per-glass-rect full-frame readback: `_engine2d_draw_ir_render_batch_embedded`,
  `val parent = eng.read_pixels_with_source()` — **line 1549**, not the ~541
  cited above (the file shifted). Needs a region-limited readback trait method
  across all 14 backends plus a device-side glass kernel.
- D6 Stage B (`simple_2d_hit_grid_u32` ID-buffer kernel) — untouched.

**L7 PORT DONE.** All 18 L7 files ported from `/home/ormastes/dev/pub/simple_l7_wt`
into the main working copy; `submit_batch` now in 22 files here (was 4), call
site at `draw_ir_adv.spl:1993`. The anti-revert protocol EARNED ITS KEEP:
`draw_ir_adv.spl` in the worktree predated a separate lane's typed
box-shadow/corner-radii feature (~112 lines) that had already landed in main —
overwriting would have silently reverted it. That one file was merged by hand
(L7 delta inserted, main content untouched); the other 17 showed 0 removed
lines. Box-shadow references verified still present post-port.

Parity specs re-run BY THE COORDINATOR in the main WC after the port:
`vulkan_engine2d_frame_batch_contract_spec` 3/3,
`engine2d_cpu_vulkan_parity_spec` 3/3,
`native_processing_ir_cuda_vulkan_readback_parity_spec` **4 total / 4 passed /
0 failed with 1 skip** — NOT the "3 total, 1 passed, 2 failed" L7 saw. The
difference is the tree, not the change: in the main WC the absent CUDA/Vulkan
devices resolve as graceful host-gated skips, in the worktree they were hard
failures. Quote the main-WC numbers.

## D1 — FIRST PRODUCTION CONSUMER (the campaign's central goal)

The whole premise was that a green event core had ZERO production consumers.
That is no longer true. `src/lib/common/ui/window_scene.spl` now imports
`draw_ir_hit_forest`/`draw_ir_node_id` (line 21) and `hit_stack` (line 22), and
`_shared_wm_taskbar_dispatch` resolves taskbar hits through the core instead of
`x / slot_w` arithmetic: it builds an ephemeral one-batch composition of 56px
slot rects, lifts it via the bridge, and resolves with `hit_stack` — the same
mechanism `draw_ir_hit_bridge_spec` and `panel2d` already prove.

Public entry `shared_wm_dispatch_pointer` is UNCHANGED. Equivalence spec
`window_scene_taskbar_hit_migration_spec` walks every 56px slot boundary
asserting the exact pre-migration action strings (`launch_app`, `focus_window`,
`unpin_app`, `pin_app`, `taskbar_empty`): **6/6**. Pre-existing
`window_scene_spec`: 11 total / 10 passed / 1 failed — the one failure
(`expected #5A7FB5 to equal #101418`, a `wm_chrome_theme()` background color) was
confirmed pre-existing by swapping in HEAD's unmigrated file and reproducing it,
and is orthogonal to dispatch.

**Pre-Wave A snapshot, superseded by the verified Wave A status below:**
deliberately left for separate reviewable steps:
`_shared_wm_content_dispatch` (window body / titlebar buttons / drag / close /
minimize) and the command-lane dispatch are still hardcoded rect tests; no wheel
branch was added, so `WINDOW_EVENT_WHEEL`/`POINTER_WHEEL` remain unconsumed by
`window_scene.spl`. Content dispatch has side effects on scene reconstruction and
wheel needs a scroll-consumption story — both are their own changes.

## Wave A (2026-07-31) — status

Landed to origin earlier: commit `b955ff755292` (42 files) carrying the core,
Panel2D, hit-query Stage A/B, D1 taskbar migration, `submit_batch`, glass region
seam, and the scroll consolidation. Verified present on `main`.

**Wave A VERIFIED — every line below re-run by the coordinator, not taken from a
lane self-report:**

| Spec | Result |
|---|---|
| `window_scene_taskbar_hit_migration_spec` | 6/6 |
| `window_scene_content_hit_migration_spec` | 9/9 |
| `window_scene_command_lane_migration_spec` | 4/4 |
| `window_scene_draw_ir_panel2d_migration_spec` | 8/8 |
| `panel2d_spec` | 15/15 |
| `window_scene_spec` | 11 total / 10 passed / 1 failed (pre-existing) |
| `window_scene_draw_ir_spec` | 12 / 9 / 3 (pre-existing, baselined) |

**D1 POINTER-DOWN IS COMPLETE; WHEEL REMAINS OPEN.** The WM's pointer-down
surface runs through the interaction core — taskbar (`_wm_taskbar_hit_slot`), window content
(`_wm_content_hit_window`: body, both close regions, minimize, drag, multi-window
z-order), and command lane (`_wm_command_lane_hit_area`). Each has an equivalence
spec asserting the public action strings are unchanged. `WINDOW_EVENT_WHEEL` /
`POINTER_WHEEL` remains R2 work in the reconciliation plan. Two dead helpers
(`_shared_wm_local_in_button`, `_shared_wm_window_contains`) were deleted; the one
surviving mention at `window_scene.spl:976` is a comment, not a call.

**D3 adoption done:** `window_scene_draw_ir.spl` derives the window embedding via
`panel_to_draw_ir_batch(...).embedding` from a composed `Panel2D`
(`_wm_window_panel2d`), replacing a hand-built `DrawIrEmbeddingConfig`. Note
Panel2D stamps `panel2d-{id}` into `surface_id`, so the window's real
`surface_id` is patched back — a gotcha for future Panel2D adopters.

Pre-existing failures baselined properly (swap in origin's blob, re-run, restore,
`cmp`-verify) rather than inferred:
- `window_scene_spec`: `expected #5A7FB5 to equal #101418`, theme projection.
- `window_scene_draw_ir_spec`: 3 failures — `retains readable bitmap text...`,
  `projects the window manager chrome...`, `keeps the no-snapshot WM Draw IR
  stream byte-compatible...` — IDENTICAL counts and names at origin.

Other Wave A outcomes:
- #5 survey → `drawir_feature_gap_2026-07-31.md` DONE, 14 ranked gaps
- Red 1 re-split → REJECTED as lossy, see below
- Red 2 → still running

**Brief error to learn from:** the internal-window lane was told to migrate
`simple_gui_internal_window` AND not to edit `window_scene.spl`. Those are
contradictory — there is no separate internal-window source file; the thing lives
inside `window_scene.spl` / `window_scene_draw_ir.spl`. Verify a target file
EXISTS before scoping a lane around it.

**Benign scare, recorded so it isn't re-investigated:** `git status` can list
`.jjconflict-side-0/` and `.jjconflict-side-1/` paths for real files while the
unresolved jj conflict commit sits in local history. That is a git-INDEX artifact.
Check for actual `.jjconflict-*` DIRECTORIES on disk and for conflict markers in
sources before concluding the tree is damaged — in this case both were clean.

## TRAP: `module_split_spec` checks SIZE, not CONTENT — a lossy split passes it

Red 1 (the browser declarations split) has now failed TWICE and is still open.

Attempt 1 landed and was verified locally, then had to be dropped from the push:
origin had grown the same file (147,122 → 157,873 B) and the two could not merge.
Origin's browser campaign actively owns that file.

Attempt 2 re-split against origin's current version and reported success —
`Results: 2 total, 2 passed, 0 failed`, both halves under the cap, function count
"preserved 30 → 30". **It had silently deleted 663 non-blank content lines
(2,988 → 2,487 lines, 157,873 → 132,028 bytes).** All 30 function NAMES survived,
so a name-based count check passed while function BODIES were gutted. Reverted
byte-identical to origin; the rejected artifacts are kept at
`lane_backup/REJECTED_decl*.spl` for post-mortem.

Two lessons, both cheap to apply:
1. **`simple_web_html_layout_renderer_module_split_spec` asserts only that files
   are under the 128 KiB cap.** It cannot detect deleted code. A green run of it
   is NOT evidence the split is lossless.
2. **Function-name counts are not a content check.** Any future split MUST verify
   line-level content preservation, e.g.
   `comm -23 <(grep -v '^\s*$' orig | sort) <(grep -v '^\s*$' split_pair | sort)`
   must be EMPTY, and total bytes must go UP (a split adds a header and a
   re-export), never down.

## D6 Stage B — DONE on the CPU backend

`src/lib/common/engine/interaction/hit_grid_u32.spl` (in `common/`, per D8).
Node ids rasterized into a u32 grid so a hit query is one texel read instead of a
CPU proxy walk. Specs, both re-run by the coordinator:
- `hit_grid_u32_spec` **7/7**
- `host_gpu_hit_query_grid_parity_spec` **4/4** — the load-bearing one: the
  grid-resolved node id EQUALS `engine2d_host_gpu_hit_query_resolve_cpu` for the
  same composition and point, miss returns the sentinel, overlapping proxies
  resolve topmost-by-layer.

**No GPU kernel was verified and none is claimed** — there is no CUDA or Vulkan
device in this environment. The CPU implementation is the executable spec the
future Vulkan/CUDA kernel must reproduce, which is the repo's established parity
pattern. Writing an unverifiable GPU kernel here would have been worth less.

## Survey item 3 was PARTLY WRONG about wheel

The survey said "`WINDOW_EVENT_WHEEL` has no consumer". That is true only of
`window_scene.spl`. The transport was ALREADY complete and working:
`window_event_adapter.spl:70-74` maps the wheel record to `PointerEvent2D` with
`kind=POINTER_WHEEL` and milli→whole delta conversion, and
`panel2d.spl:378-394` already dispatches wheel to scrollable panels with the
[0, max_scroll] clamp. So the wheel lane correctly added NO production code —
only end-to-end proof: `WindowEventRecord(WINDOW_EVENT_WHEEL, delta_y_milli=2000)`
→ drained as `delta_y=+2` → offset 0→2, plus clamps at both ends.
`panel2d_spec` is now **15/15** (13 + 2). Lesson: verify a "no consumer" claim
before commissioning work to fix it.

## A THIRD timeout mechanism exists: the test daemon

Distinct from the runner's `Process timed out` (see below) — `hit_grid_u32_spec`
failed once with `ERROR: test daemon timed out` and no `Results:` line, then
passed **7/7** on a plain retry with no code change. Daemon timeouts under
parallel-lane load are TRANSIENT. Always retry once before diagnosing.

## "Process timed out" is usually the RUNNER's limit, not a hang

The test runner enforces its OWN timeout, independent of shell `timeout`. When it
fires, the log ends in `Process timed out` with no `Results:` line — which reads
exactly like a hang. The knob is the env var **`SIMPLE_TIMEOUT_SECONDS`**.

Proven on `engine2d_read_pixels_region_equivalence_spec`: no `Results:` line and
1,900+ gc-warning lines at the default, then **3 total / 3 passed / 0 failed** at
`SIMPLE_TIMEOUT_SECONDS=1500`. It was never hung — it was outrunning the default
while ~6 lanes compiled in parallel on the same machine. Always re-test a
suspected hang with the raised limit BEFORE diagnosing a hang; this session
nearly spent a whole lane bisecting a phantom.

## D9 glass readback — DONE to priority 2

`_engine2d_read_pixels_region(engine, x, y, w, h)` added at `draw_ir_adv.spl:1537`,
call site switched at line 1673. Implemented as a FREE FUNCTION, deliberately not
a trait method: Simple traits here are pure abstract stubs with no default-body
mechanism, so the trait version would need identical additions across both tiers'
trait declarations plus ~14×2 backend impls to keep the leaf-name vtable registry
in sync — for zero behaviour gain at this stage, and with high conflict risk
against the concurrent `submit_batch` port into those same files. Built only on
existing trait methods (`read_pixels_with_source`, `width`, `height`), so it is
correct on all 14 backends. Equivalence spec 3/3 (independent index math on the
expected side, not the crop helper); `engine2d_cpu_vulkan_parity_spec` 3/3.
Priority 3 (real device-side region read) NOT done — `backend_software.spl`
stores its framebuffer `TILE_SIZE`-tiled, so a true region read needs per-tile
logic. The default still reads the full frame and crops on the host: the API seam
exists, the copy is not yet avoided.

**Regression check for the glass call site is BLOCKED, not passing.**
`draw_ir_adv_spec` (which contains the `samples_parent` glass scenarios) cannot
run: `src/lib/common/web/browser_renderer_protocol.spl` currently does not parse
(`Unexpected token: expected expression, found Newline`), so `no examples
executed`. That file is ANOTHER session's in-flight work (+850/−43 vs HEAD, no
conflict markers — a mid-edit WIP state), it is not this campaign's and must not
be touched. Re-run `draw_ir_adv_spec` once that file parses again.

Unowned reds still open (NOT caused by this campaign):
- `widget_draw_ir_theme_spec` — **ROOT-CAUSED 2026-07-31: a COMPILER DEFECT.**
  Filed as `doc/08_tracking/bug/compiler_cross_tier_diamond_import_hang_2026-07-31.md`
  with a 9-line reproducer and two passing controls, all re-verified by the
  coordinator. Trigger requires BOTH: co-importing `common.ui.widget_draw_ir`
  (imported and NEVER USED) alongside `nogc_sync_mut.ui.theme_package`, AND
  actually calling `theme_package_render_snapshot`. Drop either → passes in ~1 s.
  Suspected cause is a cross-tier diamond (common→nogc_sync_mut via
  `font_renderer`, nogc_sync_mut→common via `theme_render_snapshot`) that cycles
  the module/type resolver. Compiler-internals work, out of scope for a
  `.spl`-only campaign. The dead `slow_it` conversion was reverted; the
  reproducer is kept OUT of `test/` (it would hang the suite) at
  `scratchpad/lane_backup/compiler_bug_repro/`.
  Original characterisation below retained — it was correct:
  **a GENUINE hang, not the runner-limit phantom — the distinction was tested,
  not assumed.** Evidence: the log stops at EXACTLY 1,938 lines at the default
  limit AND at `SIMPLE_TIMEOUT_SECONDS=2000` (~33 min). Identical line count
  under a 6x larger budget means it is stuck at a fixed point in module loading,
  not making slow progress. The raised limit demonstrably works elsewhere (it
  turned `engine2d_read_pixels_region_equivalence_spec` from timeout to 3/3), so
  the var is respected and 2000s simply never arrives.
  It dies in module-graph COMPILE, not the spec body — zero examples executed.
  Spec is 15 KB, its source 17.6 KB, so size is not the cause; prime suspect
  remains the cross-tier chain from `use nogc_sync_mut.ui.theme_package`.
  Converting 8 examples to `slow_it` did NOT help (still times out on the default
  invocation) — that conversion is currently uncommitted in the spec and should
  be reverted unless a later lane finds a use for it. NOT FIXED; lane died on a
  weekly account limit mid-bisect.
  Attribution note: the deleted `zz_bisect_*` specs, the `wm_glass_theme_host_
  simpleos` docs, and the new `theme_draw_ir_material.spl` belong to a DIFFERENT
  session working the same theme subsystem — not to this campaign's lane, whose
  only edit was the spec file itself.
- `backend_lane_spec` (gc) 3 failures + `draw_ir_runtime_queue_spec` 1 failure
  (`4278190080` vs `4278255360`). **Pre-existing CONFIRMED by HEAD-baseline
  measurement** (not inference): both `backend_lane.spl` tier copies were swapped
  to their HEAD versions and the specs re-run — `backend_lane_spec` 14 total /
  11 passed / 3 failed and `draw_ir_runtime_queue_spec` 1 total / 0 passed /
  1 failed, IDENTICAL in both trees. Both files restored byte-identical (`cmp`).
  The campaign's `"hit_query"` allowlist addition caused neither.

D3 scroll consolidation DONE: all three orphaned `compositor/scroll.spl` copies
(`gc_async_mut`, `nogc_async_mut`, `nogc_sync_mut`) proven zero-caller and
deleted; `common/ui/scroll_surface.spl` kept as the consolidation target and now
has 5 real callers including `panel2d.spl` (it was down to one example before
Panel2D landed — adoption is what made it load-bearing). `scroll_surface_spec`
8/8 and `panel2d_spec` 13/13 after deletion. No FILE.md existed in those dirs.

**Deliberate D8 exception, recorded:** L4's `hit_query` allowlist entry had to go
into BOTH the `gc_async_mut` and `nogc_async_mut` copies of `backend_lane.spl`,
because the unprefixed `std.gpu.engine2d.backend_lane` alias resolves to the nogc
copy — a gc-only fix silently yielded `gpu_batched=false`. Only that one function
was synced; the remaining drift between those two files is still debt.

**Working-copy hazard hit twice this session:** an out-of-band `jj workspace
update-stale` deleted uncommitted files (sources, specs, AND this plan doc) with
no error. Recovery path that worked: `jj --ignore-working-copy --at-op=<op> file
show <path>`. All campaign files are mirrored to the session scratchpad
`lane_backup/`. A deleted spec reports as `test file not found`, NOT as a
failure — so a missing `Results:` line must never be read as "still passing".

Acceptance: every lane ships SSpec coverage; L4 keeps CPU parity spec green;
half-open bounds convention (`contains_point` left-inclusive/right-exclusive)
is the single standard (Phase-0 prerequisite from the 07-20 plan).
