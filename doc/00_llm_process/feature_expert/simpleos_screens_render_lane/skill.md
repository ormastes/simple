# SimpleOS Screens + Render Lane Feature Expert

## Role

Own feature-specific process knowledge for the **screens/render-lane** campaign:
making the WM / GUI / Web / 2D screen targets boot-selectable and runnable on
SimpleOS, unifying them on **one** render contract (`DrawIrV3Scene`) plus **one**
host HAL (`ScreenHost`), connecting real keyboard/mouse through an IRQ-backed
input path into simple-2d, removing 2D slowness at its root, and phasing a real
Vulkan (Venus / virtio-gpu 3D) driver — fail-closed evidence at every hop.

Campaign lane: `.spipe/simpleos-screens-render-lane/` (state, 10 ACs, model
policy). Status as of 2026-08-06: **PLANNED, all five detail plans complete,
implementation landing across five workstreams.**

## Pipeline Links

- [research](../../skill_command/skills/pipe/research/skill.md)
- [design](../../skill_command/skills/pipe/design/skill.md)
- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)
- [release](../../skill_command/skills/pipe/release/skill.md)
- [pipeline next step plan](../../pipeline_next_step_plan.md)

## Feature Links

- Design (authoritative current state):
  [doc/05_design/os/desktop/screen_backend_selection_and_shared_showcase.md](../../../05_design/os/desktop/screen_backend_selection_and_shared_showcase.md)
- Umbrella plan:
  [doc/03_plan/os/simpleos/screens_showcase_2d_opt_plan.md](../../../03_plan/os/simpleos/screens_showcase_2d_opt_plan.md)
- **Adversarially verified facts — trust this OVER the individual detail plans
  where they disagree:**
  [doc/03_plan/os/simpleos/screens/ws_blocker_verification.md](../../../03_plan/os/simpleos/screens/ws_blocker_verification.md)
- Cross-review: [ws_cross_review.md](../../../03_plan/os/simpleos/screens/ws_cross_review.md)
- Detail plans (`doc/03_plan/os/simpleos/screens/`):
  - WS-A config/screen selection — [ws_a_config_screen_selection_detail.md](../../../03_plan/os/simpleos/screens/ws_a_config_screen_selection_detail.md)
  - WS-B ScreenHost + shared showcase — [ws_b_screenhost_showcase_detail.md](../../../03_plan/os/simpleos/screens/ws_b_screenhost_showcase_detail.md)
  - WS-C input HAL — [ws_c_input_hal_detail.md](../../../03_plan/os/simpleos/screens/ws_c_input_hal_detail.md)
  - WS-D 2D perf/SIMD — [ws_d_2d_perf_detail.md](../../../03_plan/os/simpleos/screens/ws_d_2d_perf_detail.md)
  - WS-E Vulkan/Venus — [ws_e_vulkan_detail.md](../../../03_plan/os/simpleos/screens/ws_e_vulkan_detail.md)

## Physical 8K80 Evidence Handoff (2026-08-14)

The canonical window wrapper is
[`check-engine2d-vulkan-window-8k.shs`](../../../../scripts/check/check-engine2d-vulkan-window-8k.shs).
`ENGINE2D_VULKAN_PHYSICAL=1` is fail-closed: it uses the already-visible X11
display, requires an EDID-bearing active `7680x4320` mode at `>=80 Hz`, and validates the
backend/device identity, p95, RSS, checksum, timed-readback bytes,
completion, and fallback fields. The default wrapper starts Xvfb and is only a
device-present proxy; it is explicitly non-physical and cannot satisfy A6-A8.

The authoritative ledger is the
[render-performance plan](../../../03_plan/ui/perf/render_perf_redesign_plan_2026-08-06.md),
with operator instructions in the
[GUI/Web/2D Vulkan guide](../../../07_guide/app/ui/gui_web_2d_vulkan_setup.md)
and the open [physical-display bug](../../../08_tracking/bug/engine2d_vulkan_physical_display_8k_gate_2026-08-12.md).
The current host has no attached 8K80 mode, so A4-A8 remain active BLOCKED
rows, not exclusions:

| Row | Missing prerequisite and exact resume command | Retained record | Owner / final reviewer |
|---|---|---|---|
| A4 | Build the non-seed pure-Simple artifact with the exact command in the canonical plan, then execute `SIMPLE_NO_STUB_FALLBACK=1 timeout 300 /usr/bin/time -v -o build/render_perf/draw_ir_damage_8k_bench.time build/render_perf/draw_ir_damage_8k_bench >build/render_perf/draw_ir_damage_8k_bench.stdout 2>build/render_perf/draw_ir_damage_8k_bench.stderr` directly. | [sparse DrawIR report](../../../09_report/drawir_sparse_dynamic_8k_attempt_2026-08-12.md) and `doc/08_tracking/bug/self_hosted_cli_native_build_silent_no_artifact_2026-08-14.md` | pure-Simple native-build owner / separate highest-capability Codex reviewer |
| A5 | With the admitted compiler, run `BENCH_TIMEOUT_SECS=300 BUILD_DIR=build/render_perf/gui_8k80 REPORT_PATH=build/render_perf/gui_8k80/gui_8k80_semantic_producer.md bash tools/gui_perf_bench/run_all_benchmarks.shs --width 7680 --height 4320 --frames 60 --dpi 300`; require the native semantic producer route with no seed/interpreter fallback. | `build/render_perf/gui_8k80/gui_8k80_semantic_producer.md` and sibling receipts; [retained Web report](../../../09_report/web_renderer_retained_damage_plan_evidence_2026-08-12.md) | UI render producer owner / separate highest-capability Codex reviewer |
| A6 | Resume canonical Todo DB item TODO684 when the physical 8K80 display is attached. | [physical-display bug](../../../08_tracking/bug/engine2d_vulkan_physical_display_8k_gate_2026-08-12.md) and `build/check/engine2d-vulkan-window-8k/` | physical display operator / separate highest-capability Codex reviewer |
| A7 | After A4-A6 are admitted, rerun each canonical row once and require p95 `<=12500000 ns`, no CPU/interpreter/stub fallback, known completion, and complete receipts. | [render-performance plan](../../../03_plan/ui/perf/render_perf_redesign_plan_2026-08-06.md) | root Codex merge owner / separate highest-capability Codex reviewer |
| A8 | Resume canonical Todo DB item TODO685; its hardware-aware checker owns retained connector, EDID, and presentation evidence without claiming captured-scanout parity. | [physical-display bug](../../../08_tracking/bug/engine2d_vulkan_physical_display_8k_gate_2026-08-12.md) | physical display operator / separate highest-capability Codex reviewer |

The Xvfb receipt remains useful only as a regression check and must be labeled
`scope=xvfb-device-present-proxy`; it cannot promote the umbrella 8K80 feature.

## Affected Layers

- [layer_expert/ui_render](../../layer_expert/ui_render/skill.md) — `DrawIrV3Scene`,
  `RenderBackend`, `WidgetNode`, Engine2D pixel/blend kernels.
- [layer_expert/os_compositor](../../layer_expert/os_compositor/skill.md) —
  `CompositorBackend`, boot screen selection, WM lane.
- Adjacent (do not duplicate their scope):
  [wm_gui_window_drawing](../wm_gui_window_drawing/skill.md),
  [simpleos_wm_qemu_evidence](../simpleos_wm_qemu_evidence/skill.md),
  [rendering_inside_rendering](../rendering_inside_rendering/skill.md),
  [interaction_input_routing](../interaction_input_routing/skill.md).

## Load-Bearing Facts (read before writing any code here)

These are the things a fresh agent otherwise burns a session rediscovering. All
were verified against source, several by refuting an earlier planning claim.

1. **`DrawIrV3Scene` is the shared render contract.** GUI and Web already both
   produce it. **`app.ui.render` is an unrelated text/HTML string contract — do
   NOT build the screen lane on it.** It is an explicit scope exclusion.
2. **`RenderBackend` has 8 importers and is *never implemented*.** The ~15
   `std.gpu.engine2d.backend` files carry a *same-named but different* trait —
   do not conflate them when counting or grepping.
3. **`ScreenHost` lands additively — never as a rename** of `RenderBackend` or
   `CompositorBackend`. Its contract is `size()` + `present_scene(DrawIrV3Scene)`
   + `poll_input() -> HostInputEvent?`, and it must be the ONLY per-target code
   (AC-3 is proven by a dependency check, not by inspection). Four thin impls are
   planned: wm (`wm_app_process_contract`), gui (SDL2/winit `GuiRenderer`), web
   (`ui.web`), 2d (engine2d framebuffer).
   > **UNRESOLVED CONFLICT — do not pick a side silently.** The design doc
   > describes `trait ScreenHost` as a **renamed/extended `RenderBackend`** in
   > `src/lib/common/ui/backend.spl`, while the campaign's standing instruction
   > is that it lands **additively, never as a rename**. `RenderBackend` has 8
   > live importers (listed in fact 2), so a rename is a breaking change to all
   > of them. Treat additive-plus-adapter as the default and get this reconciled
   > before touching `backend.spl`.
   `HostInputEvent` (new, `src/lib/common/ui/`) =
   `Pointer{x,y,button,pressed,wheel}` | `Key{code,ch,down,mods}` | `Resize{w,h}`.
4. **Factory arms are not uniform.** `FramebufferBackend` implements
   **`RenderBackend`** at `fb_backend.spl:133` — **not** `CompositorBackend`
   (which is *declared* at `display_backend_core.spl:7` and not implemented
   there). Earlier plans cite `fb_backend.spl:121`; that line number is wrong.
   Never assume every backend behind the factory satisfies the same trait.
5. **`WidgetNode` is a handle over a module-global store.** Showcase logic is
   therefore **"no I/O", not pure**. Consequence for tests: specs must use
   **distinct widget-id prefixes or they collide** across examples/files.
6. **There is no `HalInput` trait, and the ruling is not to add one.**
   `hal_current.spl:36` is x86_64-hardwired. **`InputBackend`
   (`src/os/compositor/input_backend.spl`) stays the abstraction** — do not
   invent a parallel one. IRQ wiring reuses the existing
   `HalInterrupt.interrupt_set_handler` chain (`hal.spl:128` → `:386` →
   `hal_current.spl:159` → `arch_adapt/x86_64/interrupt.spl:27`); drivers split
   into `isr_ingest()` / `decode_pending(queue)`, and `SIMPLE_PS2_IRQ=off` must
   produce an identical transcript.
   Related input state: PS/2 keyboard+mouse are polled-only (no IRQ1/IRQ12),
   `InputEventQueue` has zero consumers, and two incompatible `MouseEvent` types
   exist (AC-6 unifies them).
7. **Pixels are boxed `int64_t`** via `engine2d_box_pixel` / `engine2d_unbox_pixel`
   (`runtime_simd_dispatch.c:663`/`:667`) — **NOT packed u32.** *Any WS-D SIMD
   kernel design that assumes packed u32 lanes is invalid.* Blend allocates on
   the native path too: two `malloc`s plus three O(n) passes per blended row
   (`:1464-1476`), and the malloc-failure fallback is *also* per-pixel
   unbox/blend/box — so there is currently **no allocation-free path at all**.
   D2 must either box-aware-unpack once per span or attack the boxing itself.
8. **`dirty_tiles` are marked at 6 sites and read by nobody.** Damage-driven
   present (AC-7) is a matter of *consuming* an existing signal, not adding one.
9. **Venus is fully modeled.** The multiconfig bridge gate
   (`check_simpleos_multiconfig_live_evidence.spl:145`) **hard-equals the legacy
   `disable-modern=on` 2D device and therefore cannot prove a Vulkan claim.**
   Scope: this reaches only `derived_engine2d_vulkan_bridge_status` (:138); the
   primary `derived_engine2d_vulkan_status` (:117) never consults the device
   string — the earlier "every Vulkan claim is false" framing was overstated.
   Any fix must **tighten** (block a Vulkan claim asserted on the 2D device),
   never loosen. AC-9 also requires modeled responses be *removed, not relabeled*.
10. **The 4 specs importing the nonexistent `common.ui.backend_factory` FAIL
    LOUDLY** (`no examples executed` / `1 total, 0 passed, 1 failed`). The
    earlier claim of *silent false coverage* was **empirically refuted** — and
    the count is **four** importers, not seven (three further files only mention
    it in `@cover` comments, the likely miscount source). Still worth fixing;
    not a fail-open hole.
11. **`ShowcaseSurface` needs a schema change before AC-4 can pass.** It is
    exactly `Standalone|HostWm|SimpleOsWm` with three `*_ready` bits, and
    `showcase_surface_supported` matches exhaustively — `Web`/`Raw2d` variants
    must land before any readiness bit can represent four targets.
12. **Keytype-on-WM is NOT blocked** (refuted). `wm_fs_key_event:241` already
    ships keycodes across the WM boundary as `kind="key"` + `button=keycode`, and
    the encoder/decoder round-trips `button`. The residual gap is narrow: no
    character, modifier, or wheel encoding — a small WS-B/B1 encoding task.
13. **Boot selection gap.** `CompositorBackend` has 6+ implementors; what is
    missing is a factory + boot selection — `init_services.spl:179`
    (`_init_display_service()`) hardcodes BGA 1024x768, and `rc_conf.spl` is
    boolean-only + key-whitelisted, so it cannot express `screen_type` today.
    WS-A adds string keys + `rc_conf_value(key) -> text?`, a new
    `src/os/compositor/backend_factory.spl` registry, and a `SIMPLE_SCREEN_TYPE`
    env mirror.
14. **A real duplicate Engine2D implementation exists.** Canonical is
    `src/lib/nogc_sync_mut/gpu/engine2d/`; `src/lib/nogc_async_mut/gpu/engine2d/`
    is a duplicate slated for deletion. Do not "fix" both — and remember that
    deleting a reimplementation *reroutes* callers rather than deduping them.
15. **Vulkan surface area is tiny and modeled.** Only opcodes `0x0100`–`0x0107`
    plus cursor exist (`virtio_gpu_types.spl:13-20`); feature negotiation acks
    nothing (`virtio_gpu_init.spl:48-57`); `vulkan_icd_virtio.spl` is 182 lines
    fully modeled (`_venus_transport_send:52` returns a fake handle, with an
    invented opcode enum). Corrected QEMU args for a real path:
    `virtio-gpu-gl-pci,hostmem=256M,blob=true,venus=true,context_init=true` with
    `-display sdl,gl=on` or `egl-headless,gl=on`, and virglrenderer built
    `-Dvenus=true`. **llvmpipe must yield `blocked:software-renderer`, never a
    pass.** Open: the Venus capset v0 ring-layout header is unverified against
    the spec.

## Verification Requirements

- **No claim without its artifact.** AC-2 requires a nonblank QMP screendump +
  serial marker *per screen type*; AC-7 requires a before/after bench row from a
  **pinned worktree + deployed native binary** (p50 baseline: 2389 ms vs Cairo
  0.032 ms); AC-10 forbids mock-in-the-middle, fixture-only renderer bypass, and
  any readiness bit flipped without a captured artifact.
- Board-runnable rule applies: virtio-gpu is a QEMU device, so the physical-board
  GPU display gap is **filed explicitly**, not implied away
  (`.claude/rules/board-runnable.md`).

## Related Lanes (do not duplicate)

`wm_gui_web_2d_host_env_hardening`, `simpleos-multiconfig-vulkan-wm`,
`simple-wm-host-simpleos-fullscreen`, `simpleos-qemu-wm-real-screen`,
`simple-gui-2d-render-perf`, `web-wm-authoritative` (CLOSED).

## Update Rule

When the project process creates or changes research, requirements,
architecture, design, tests, implementation, verification, or release artifacts
for this feature, update this skill with the new links and the current handoff
notes. In particular: when a workstream lands, record which of the load-bearing
facts above it *invalidates* — several are already corrections of earlier plan
text, and a stale fact here is worse than none.

Template: `.spipe/spipe/doc/00_llm_process/template/feature_skill.md`
