# Plan: SimpleOS Screen Types + Shared Showcases + Input HAL + 2D Optimization + Vulkan

Date: 2026-08-06. Design: `doc/05_design/os/desktop/screen_backend_selection_and_shared_showcase.md`.
Related: `doc/03_plan/os/simpleos_multiconfig_vulkan_wm_plan.md` (evidence gates — reused, not duplicated).

Model policy: default **sonnet** for well-scoped implementation; **opus** for
kernel/IRQ work, native+interpreter SIMD kernels, interface design, and Venus
transport. Tasks marked (S)=sonnet, (O)=opus. Independent workstreams run in
parallel; inside a workstream, tasks are ordered by dependency.

## Workstream A — Config + screen-type selection (parallel-safe)

| ID | Task | Files | Model |
|----|------|-------|-------|
| A1 | rc.conf string values: accept `screen_type`, `screen_res`, `screen_simd`; add `rc_conf_value(key)->text?`; keep booleans intact; unit spec | `src/os/kernel/boot/rc_conf.spl`, `test/01_unit/os/kernel/boot/rc_conf_spec.spl` | S |
| A2 | `CompositorBackend` factory registry keyed by screen_type; fail-closed vs `SimpleOsRuntimeProfile` caps, fallback `wm`; unit spec with fake profile | new `src/os/compositor/backend_factory.spl` | S |
| A3 | Wire `_init_display_service()` to factory (default `wm` preserves today's boot); `SIMPLE_SCREEN_TYPE` env mirror for host harness | `src/os/kernel/boot/init_services.spl:179` | S |
| A4 | QEMU boot evidence: each of 4 screen types boots, QMP screendump nonblank, serial marker per type; feed multiconfig evidence keys | `scripts/check/` wrapper reuse | S |

Deps: A1→A2→A3→A4.

## Workstream B — ScreenHost interface + shared showcases (B1 first, rest parallel)

| ID | Task | Files | Model |
|----|------|-------|-------|
| B1 | Design+land `ScreenHost` (extend `RenderBackend`): `present_scene(DrawIrV3Scene)`, `poll_input()->HostInputEvent?`; define `HostInputEvent` (one Pointer type — kills the dual MouseEvent); migration note for 7 importers | `src/lib/common/ui/backend.spl`, new `src/lib/common/ui/host_input_event.spl` | **O** |
| B2 | `showcase_core.spl`: shared widget tree — toolbar, scroll panel + scrollbar, two linked panels (scroll-sync), event probe pane (click/drag/keytype log). Pure; imports only common/ui + ScreenHost | new `src/app/ui_showcase/showcase_core.spl` | S |
| B3 | 2D host impl + 2d showcase main (engine2d fb present, direct input) | `src/app/ui_showcase/main_2d.spl` | S |
| B4 | GUI host impl + main (SDL2/winit window via `GuiRenderer`), fix `examples/06_io/ui/widget_showcase_gui.spl` to shared pipeline | `src/app/ui_showcase/main_gui.spl` | S |
| B5 | Web host impl + main (internal window widget, scrollpane+bar) on `ui_web_packed_producer` path | `src/app/ui_showcase/main_web.spl` | S |
| B6 | WM host impl + main via `wm_app_process_contract` (windows + toolbar widget on WM) | `src/app/ui_showcase/main_wm.spl` | S |
| B7 | Arch dependency check: showcase modules import only render land + ScreenHost (no direct engine2d/SDL/OS imports outside host impls); wire into lint/check | `scripts/check/` or arch spec | S |
| B8 | Evidence: play_sdl2/play_wm screenshots + event transcripts per target; flip `showcase_catalog.spl` readiness bits only with evidence | `src/lib/common/ui/showcase_catalog.spl` | S |

Deps: B1→(B2..B6 parallel)→B7,B8.

## Workstream C — Input drivers + HAL (parallel with A/B; C1 after B1)

| ID | Task | Files | Model |
|----|------|-------|-------|
| C1 | Unify event types: rewrite dead `input_event.spl` queue around `HostInputEvent`; delete duplicate MouseEvent; migrate `InputBackend` impls + compositor `handle_input` | `src/os/drivers/input/input_event.spl`, `src/os/compositor/input_backend.spl`, `compositor.spl:942-1000` | **O** |
| C2 | IRQ1/IRQ12 handlers via `HalInterrupt.interrupt_set_handler` → event queue; polling kept as fallback behind same queue API; QEMU proof (typed chars + pointer deltas over serial/QMP) | `src/os/kernel/interrupts/`, `ps2_keyboard.spl`, `ps2_mouse.spl` | **O** |
| C3 | Mouse wheel end-to-end: PS/2 Z-byte packet, wheel field in HostInputEvent, scroll dispatch to widget layer; closes `wm_mouse_wheel_events_dropped_2026-07-05` | `ps2_mouse.spl`, widget_hit path | S |
| C4 | SDL2 host `InputBackend` impl (gap: winit-only today) | new `src/os/compositor/hosted_input_sdl2.spl` | S |
| C5 | Connect input → simple-2d screen: 2d screen app consumes queue; QEMU evidence of click/drag/keytype reaching showcase probe pane | glue in A2 screen app | S |

Deps: B1→C1→(C2,C3,C4 parallel)→C5.

## Workstream D — 2D performance (independent; ordered by measured impact)

| ID | Task | Files | Model |
|----|------|-------|-------|
| D0 | Baseline bench on pinned worktree, native self-hosted binary; record numbers (fill/copy/blend/blit/full-frame) before any change | `test/perf/graphics_2d/bench_harness.spl` | S |
| D1 | In-place `blend_span` + `blit_row` native kernels (SSE2 baseline + AVX2 dispatch); route `simd_kernels.spl`; delete gather/scatter blend at `simd_kernels.spl:372-392`, `backend_software.spl:621/:764`; fix `simd_fill_row` copy-back; fix facade inconsistency (canonical owner `nogc_sync_mut/gpu/engine2d/`) | `src/runtime/runtime_simd_dispatch.c`, `nogc_sync_mut/gpu/engine2d/simd_kernels.spl`, `backend_software.spl` | **O** |
| D2 | Interpreter extern bridge O(count): in-place ops on rt array buffer, kill unpack/pack of whole framebuffer per span | `src/compiler_rust/compiler/src/interpreter_extern/simd.rs:1403-1414` | **O** |
| D3 | Damage-driven present: read `dirty_tiles` (already marked), `get_dirty_tiles()` → `present_rect` per tile; widget bbox invalidation feeds marking | `backend_software.spl:478`, `compositor/tile.spl:102` | S |
| D4 | Opaque/transparent fast paths + premultiplied ARGB internal format; per-surface opaque flag; `read_pixels` bulk copy | `backend_software.spl` | S |
| D5 | SIMD config: `screen_simd`/`SIMPLE_2D_SIMD` = `auto|off|sse2|avx2|neon` + per-kernel toggles; default off under interpreter until D2 proves otherwise | `simd_kernels.spl`, `renderer_select.spl`, A1 key | S |
| D6 | Per-window backing store + occlusion culling + scroll-by-copy in WM compositor | `wm_core.spl`, `compositor.spl` | **O** |
| D7 | Glyph atlas (A8, shelf packer) + masked SIMD text blit | engine2d + text path | S |
| D8 | Re-bench after each of D1–D7; final report with before/after table; file regressions immediately | `doc/09_report/` | S |

Deps: D0→D1→(D2,D3,D4,D5 parallel)→D6→D7→D8. Gate: every task lands with its bench delta.

## Workstream E — Vulkan on SimpleOS (independent; QEMU-scoped)

| ID | Task | Files | Model |
|----|------|-------|-------|
| E1 | virtio-gpu 3D: negotiate VIRGL/Venus feature bits + capset query on existing driver | `src/os/drivers/virtio/virtio_gpu*.spl` | **O** |
| E2 | 3D context create + Venus ring transport over ctrlq (MapBar/AllocDma syscalls 83/84 already exist) | same + `syscall_shim_device.spl` | **O** |
| E3 | Point `vulkan_icd_virtio.spl` at real transport; replace modeled responses; minimal proof = device enumerate + clear + readback checksum | `src/lib/nogc_async_mut/gpu/vulkan_icd_virtio.spl` | **O** |
| E4 | Feed multiconfig evidence gates (Engine2D Vulkan, readback, RenderDoc rows). **Board-runnable note:** virtio-gpu is QEMU-only by nature; file the physical-GPU gap explicitly per `.claude/rules/board-runnable.md` — do not imply board support | evidence wrappers | S |

Deps: E1→E2→E3→E4.

## Parallelization summary
- Start immediately in parallel: **A1, B1, D0/D1, E1**.
- After B1: fan out B2–B6 (5 parallel sonnet tasks) + C1.
- A, C, D, E are mutually independent; B blocks on B1 only.
- Critical path: B1 → C1 → C2 → C5 (input on real screen) and D1 → D3 → D6 (perf).

## Successor perf/compiler plan (2026-08-06)

The deeper render-performance redesign now lives in
`doc/03_plan/ui/perf/render_perf_redesign_plan_2026-08-06.md` (diagnosis:
`doc/01_research/ui/perf/render_perf_diagnosis_2026-08-06.md`). It supersedes
this plan's WS-D damage-consumer and SIMD-knob mechanisms (see its §12
reconciliation table); WS-A/B/C/E stay authoritative here. Its performance
critical path is F1 (class reference semantics) → F2 (packed span ABI) →
F3 (direct column arena writer).

## Global gates
- Each fix pushed to GH immediately after landing (standing rule).
- Bench evidence on pinned worktree + deployed native binary only (measurement-trap rules).
- No task flips a readiness/evidence bit without a captured artifact.
- Failing tests never skipped; grammar/perf issues hit during work get filed, not normalized.
