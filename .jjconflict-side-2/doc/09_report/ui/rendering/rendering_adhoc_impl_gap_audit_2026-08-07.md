# Rendering Stack Ad-Hoc Implementation / Gap Audit — 2026-08-07

Scope: `src/lib/{gc_async_mut,nogc_sync_mut,common}/gpu/engine2d/**`,
`src/lib/common/ui/render_opt/**`, `src/lib/gc_async_mut/gpu/browser_engine/**`
(rendering-relevant), `src/os/compositor/**`, `src/lib/nogc_sync_mut/text_layout/**`.
Excluded (collisions with concurrent sessions): `backend_software.spl`
`ensure_kernel_table`, `src/app/ui_showcase/hosts/host_wm.spl`,
`window_scene_draw_ir.spl`, `style_block.spl`. Vendored code excluded.

Method: systematic grep (`pass_todo|pass_do_nothing|pass_dn`, `TODO|FIXME`,
stub keywords, literal-return bodies, bare early returns mapped to enclosing
functions, hardcoded dimensions, locally redefined constants), then each lead
read in context. Binary: `bin/simple` →
`bin/release/x86_64-unknown-linux-gnu/simple` (self-hosted, not seed).

**Counts: 13 confirmed findings — 3 fixed, 3 filed, 7 false-positive.**

## FIX-NOW (fixed in this pass)

### 1+2. Silent glyph-slot caps in backend font offload probes
`src/lib/nogc_sync_mut/text_layout/font_rasterizer.spl`
(`_try_vector_font_glyph_from_backend`, was lines 331–366;
`_try_bitmap_font_glyph_from_backend`, was lines 720–739; all four lib tiers
forward here, so one fix covers the family).
- Evidence: both loops were hand-unrolled `if glyph_count > N` chains — vector
  stopped at slot 7, bitmap at slot 3 — so a backend publishing
  `GLYPH_COUNT` > cap had its higher slots silently dropped (no counter, no
  log), and the two caps had already drifted apart (8 vs 4).
- Fix: replaced both unrolls with a bounded `while` loop over `"{slot}"`
  honoring `GLYPH_COUNT`, clamped by a new shared explicit
  `_FONT_GLYPH_SLOT_CAP = 64` (guards against garbage env counts).
- Spec: `test/01_unit/lib/common/text_layout/font_glyph_slot_loop_spec.spl` —
  publishes a checksum-valid bitmap glyph at slot 5 with count 6 (unreachable
  under the old 4-slot cap) and a huge-count no-match fallback case.
  Result: `Results: 2 total, 2 passed, 0 failed`. Sabotage (cap forced to 4):
  slot-5 case fails `expected 1 to equal 0` (CPU fallback taken), restore →
  green. Pre-existing `bitmap_font_gpu_offload_spec.spl` still green (2/2).

### 3. `pump_host_events` silent always-0 no-op
`src/os/compositor/host_compositor_core.spl:2193` (`HostWmHandle.pump_host_events`).
- Evidence: body was `if self.event_loop_id == 0: return 0` then `0` — a
  function named "pump host events" that unconditionally returns 0 with no
  observability, called every `tick_forever` iteration.
- Analysis: only Headless handles are ever constructed here
  (`init_headless_host_wm`), and no backend reachable from this file exposes a
  host event source, so 0 events is *correct* — but it was a silent fake
  rather than the repo's counted-no-op pattern.
- Fix: added module-level `_host_wm_event_pump_noop_ticks` +
  `host_wm_event_pump_noop_ticks()` accessor (module var + free function,
  respecting the F1 class-field workaround), incremented per live-handle tick,
  plus an honest docstring.
- Spec: `test/01_unit/os/compositor/host_wm_event_pump_honesty_spec.spl` —
  `Results: 1 total, 1 passed, 0 failed`. Sabotage (increment removed): fails
  on the counter assertion, restore → green.

## FILE (real, larger than this pass)

### 4. `bridge_drawing_compositor.spl:73` — TODO(blend-mode)
`src/lib/gc_async_mut/gpu/engine2d/bridge_drawing_compositor.spl:73`.
Engine2D exposes only Normal (src-over) blending; the drawing compositor's 13
blend modes must be pre-flattened by the caller. Real gap: Engine2D-level blend
mode support (multiply/screen/overlay/... kernels per backend) so the bridge
can reproduce non-Normal layers itself. Needs new blend kernels in
engine/backends + kernel_registry op coverage — well beyond 20 lines.

### 5. `bridge_drawing_compositor.spl:77` — TODO(layer-position)
Same file, line 77. `DrawingLayer` in `std.common.drawing.document` has no x/y
offset (layers are full-canvas), so positioned sublayers are unrepresentable in
this bridge. Needs a document-model change (layer origin fields) plus
`draw_image(x, y, ...)` per-region bridging — cross-module model change, filed.

### 6. `backend_emu.spl:644` — TODO(perf) gradient stop LUT
`src/lib/gc_async_mut/gpu/engine2d/backend_emu.spl:644`. Per-pixel linear
search over gradient stops; a 1001-entry permille LUT would be O(1)/pixel and
bit-exact (positions already integer permille). Correct today, hot-loop perf
work with a required bit-exactness proof against `scalar_oracle` — filed rather
than rushed.

## FALSE-POSITIVE (looked ad-hoc, deliberate on inspection)

7. `src/os/compositor/frame_pacer.spl` — monotonic-clock budget sleep instead
   of real vsync. Extensively documented honest gate: header proves (via
   virtio_gpu ops audit) no scanout/vblank signal exists at this tier and
   explicitly forbids faking one; upgrade path recorded.
8. `pass_do_nothing` hits (engine.spl:402/1103, backend_session.spl:198,
   bridge_game2d.spl:75, browser_engine js/*) — all are explicit no-op match
   arms or documented no-op contracts with reason strings; none replace a
   promised computation.
9. Literal-return tiny bodies (backend_vulkan_font.spl:37/227,
   browser_engine net/h1_client, h2_frame, ws_utils, dom_color.spl:255,
   html_tree_builder.spl:124/155, layout renderer hex/dec val) — guard clauses
   and char/keyword lookup tables; real computation follows.
10. `src/os/compositor/engine2d_render_evidence.spl:25`
    `SIMPLEOS_RENDER_FORMAT_ARGB8888 = 1u32` — not a duplicate of
    `kernel_registry` format codes (different namespace: baremetal render
    receipt `format_code`, validated `> 0` by
    `backend_render_receipt.spl:64`); single definition, no drift pair exists.
11. `hosted_backend_cocoa.spl` / `hosted_backend_win32.spl` /
    `arm64_virtio_input_backend.spl` — documented honest `-1/false` sentinel
    stubs behind genuine runtime OS checks (their own comments call out the
    honest-stub contract).
12. `vulkan_compositor_backend.spl` — honestly-gated backend
    (`is_available()==false` + counted `reject(op)`); per task definition, not
    a violation.
13. `host_compositor_core.spl` `host_background_crop_surface` — out-of-range
    reads degrade to opaque black, but the degradation is documented, bounded,
    and by construction unreachable (surface sized to resolver dimensions).

## Known-collision items verified open but skipped (other agents mid-flight)
- `backend_software.spl` KERNEL_BUCKET gate probing only `fill_const` — skipped.
- `host_wm.spl` per-pixel readback — skipped.
- `style_block.spl` — uncommitted-hazard file, untouched.
