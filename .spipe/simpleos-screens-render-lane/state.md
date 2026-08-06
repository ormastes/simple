# Feature: SimpleOS Screens + Render Lane Runnable & Hardened

## Raw Request
> make deep research and plan with agents, simple os to have configs, 2d rendering
> screen, web rendering screen, gui rendering screen, and existing default wm screen.
> in 2d showcase check events/click/drag/keytype, panel with scrollbar, linked panels,
> windows and widget (toolbar) on wm. web render showcase internal window widget,
> scrollpane and bar, similar to gui and wm. check only depends render land and
> dedicated host interface, and use almost all same logic and code except HAL.
> check simple keyboard mouse driver and HAL layer connected to simple 2d. vulkan
> driver on simple os. and optimize simple 2d SIMD backed (config detail simd) — it
> is too slow, analyze and optimize, check buffer and other optimization is not
> applied, research 2d optimizations and apply. make research, update design and
> detail parallel plan; detail so mostly sonnet can do, assign difficult to opus.
>
> Follow-up: `$sp_dev` — complete wm and render lane SimpleOS-runnable and harden
> plan. complete the detail plans in parallel agents.

## Task Type
feature

## Refined Goal
Make the WM/GUI/Web/2D render lane selectable and runnable on SimpleOS via boot
config, unify the four screen targets on one `DrawIrV3Scene` render contract plus a
single `ScreenHost` HAL, connect real keyboard/mouse input through an IRQ-backed HAL
path into simple-2d, remove the measured 2D slowness at its root (in-place SIMD
kernels, damage-driven present, backing stores, glyph atlas), and phase a real
Vulkan (Venus/virtio-gpu 3D) driver — with fail-closed evidence at every hop.

## Status: PLANNED — all five detail plans complete (2026-08-06); ready to implement

## Blockers found during detailed planning (fix before the AC they gate)
1. **AC-9 gate is structurally false today**: `check_simpleos_multiconfig_live_evidence.spl:145`
   hard-equals `virtio-gpu-pci,disable-modern=on,disable-legacy=off` — the legacy 2D
   device, which can never expose a Venus capset. Fix with a lane-keyed allow-list
   that *tightens* (blocks a Vulkan claim asserted on the 2D device), never loosens.
2. **AC-5 keytype-on-WM is physically blocked**: `WmFsAppEvent` has no key/char/wheel
   field. B1 extends it; B6 must not claim keytype before that lands.
3. **Seven specs are fail-open**: they `use` a `common.ui.backend_factory` that does
   not exist; unresolved `use` is only a WARN. They prove nothing and may not be
   cited as coverage. File as a bug.
4. **AC-4 readiness bits unimplementable as written**: `ShowcaseSurface` is
   `Standalone|HostWm|SimpleOsWm` — needs `Web`/`Raw2d` variants first.
5. **Blend is allocation-bound on the NATIVE path too**, not just interpreted
   (`runtime_simd_dispatch.c:1454` mallocs two scratch buffers, unbox/reboxes per
   pixel). Pixel words are boxed `int64_t`, not packed `uint32_t` — every new kernel
   must respect that or the boxing itself becomes the lever.

## Research (complete, 2026-08-06)
Five parallel agent sweeps. Full findings in the design doc:
`doc/05_design/os/desktop/screen_backend_selection_and_shared_showcase.md`.

Load-bearing facts:
- `CompositorBackend` trait already exists with 6+ implementors; the gap is a
  factory + boot selection (`init_services.spl:179` hardcodes BGA 1024x768).
- rc.conf is boolean-only + key-whitelisted; cannot express `screen_type` today.
- `DrawIrV3Scene` is the real shared render contract — GUI and Web already both
  produce it. `RenderBackend` is imported by 7 targets but **never impl'd**.
- PS/2 keyboard+mouse exist but polled-only (no IRQ1/IRQ12); no `HalInput`;
  `InputEventQueue` has zero consumers; two incompatible `MouseEvent` types.
- 2D slowness root causes: interpreter extern bridge repacks whole framebuffer per
  span; SIMD alpha-blend is net-negative (gather/scatter, no in-place `blend_span`);
  `simd_fill_row` slower than scalar; blit never SIMD; `dirty_tiles` marked but read
  by nobody; no batching/double-buffer. Evidence: p50 2389 ms vs Cairo 0.032 ms.
- virtio-gpu 2D driver + MapBar/AllocDma syscalls real; Vulkan/Venus is stubbed.

## Acceptance Criteria
- AC-1: `/etc/rc.conf` `screen_type="wm|2d|web|gui"` selects the boot screen through a
  `CompositorBackend` factory, fail-closed against `SimpleOsRuntimeProfile` caps with
  documented fallback; default `wm` preserves today's boot exactly.
- AC-2: All four screens boot in QEMU with nonblank QMP screendump + serial marker
  evidence per screen type; no screen type may claim pass without its artifact.
- AC-3: One `ScreenHost` interface (`present_scene(DrawIrV3Scene)` + `poll_input()
  -> HostInputEvent?`) is the ONLY per-target code; a dependency check proves showcase
  modules import only render-land + `ScreenHost`.
- AC-4: One shared `showcase_core` (toolbar, scrollpane+scrollbar, linked panels,
  event probe) renders on all four targets from byte-identical logic; the existing
  hand-drawn `widget_showcase_gui.spl` is migrated onto the shared pipeline.
- AC-5: Click, drag, and keytype originating at the real host/driver boundary are
  observed in the showcase probe pane on every target, with captured transcripts.
- AC-6: Keyboard+mouse reach simple-2d through one event type and one queue: dual
  `MouseEvent` removed, `InputEventQueue` revived with real consumers, IRQ1/IRQ12
  handlers registered with polling retained as fallback, mouse wheel fixed end-to-end.
- AC-7: 2D perf: in-place `blend_span`/`blit_row` native kernels replace all
  gather/scatter paths, interpreter extern bridge is O(count) not O(framebuffer),
  damage-driven present consumes the already-marked dirty tiles, and every change
  lands with a before/after bench delta from a pinned worktree + deployed native
  binary. No claim without a bench row.
- AC-8: SIMD is configurable (`screen_simd`/`SIMPLE_2D_SIMD` = auto|off|sse2|avx2|neon
  plus per-kernel toggles) and the interpreted default is chosen by measurement.
- AC-9: Vulkan on SimpleOS negotiates real virtio-gpu 3D/Venus capsets, submits over a
  real ring transport, and proves device-origin readback; modeled responses are removed,
  not relabeled. QEMU-scoped with the physical-board gap filed explicitly.
- AC-10: Every AC has an SSpec scenario with real assertions; no mock-in-the-middle, no
  fixture-only renderer bypass, no readiness bit flipped without a captured artifact.

## Scope Exclusions
- TUI cell-grid → DrawIrV3 bridging (stays as-is).
- `app.ui.render` string contract (untouched).
- virgl full GL — Venus/Vulkan path only.
- Physical-board GPU display evidence (virtio-gpu is a QEMU device; gap filed per
  `.claude/rules/board-runnable.md`).

## Plans
- Umbrella: `doc/03_plan/os/simpleos/screens_showcase_2d_opt_plan.md`
- Detail (per workstream, `doc/03_plan/os/simpleos/screens/`):
  - `ws_a_config_screen_selection_detail.md`
  - `ws_b_screenhost_showcase_detail.md`
  - `ws_c_input_hal_detail.md`
  - `ws_d_2d_perf_detail.md`
  - `ws_e_vulkan_detail.md`

## Related Lanes (do not duplicate)
`wm_gui_web_2d_host_env_hardening` (test_host_env + coverage ACs),
`simpleos-multiconfig-vulkan-wm` (evidence gates/wrappers),
`simple-wm-host-simpleos-fullscreen` (host/SimpleOS fullscreen WM),
`simpleos-qemu-wm-real-screen` (ARM64 real-screen evidence),
`simple-gui-2d-render-perf`, `web-wm-authoritative` (CLOSED).

## Model Policy
Sonnet by default with per-task file lists and explicit acceptance. Opus for:
`ScreenHost`/`HostInputEvent` interface design, input event-type unification, IRQ
wiring, native+interpreter SIMD kernels, compositor backing-store/occlusion, and the
Venus transport.
