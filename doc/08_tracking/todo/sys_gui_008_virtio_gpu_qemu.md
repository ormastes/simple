# SYS-GUI-008 virtio-gpu Accelerated Path in QEMU (V1) — Tracker (2026-04-14)

**Status:** not yet started. This is the first planning pass for Row 4 of
`doc/03_plan/gui_drawing_layer_variations.md` (line 133). sys-gui-008
delivers the virtio-gpu accelerated baseline for SimpleOS V1, so the
same desktop scene that sys-gui-006 renders over the BGA framebuffer
also renders green through `VirtioGpuBackend` + `GpuCompositorBackend`
end-to-end in QEMU, under the same compositor and wm contract.

## Scope

Prove V1's virtio-gpu lane from PCI probe to on-screen scanout in
QEMU, wired through the locked `Compositor` + `Engine2D` trait
surfaces, and gated by a system test with a committed PPM baseline
(mirroring sys-gui-006). Out of scope: 3D/virgl, cursor hotspot
resources, multi-display scanout, real hardware GPUs, host-OS hosted
backends (V2 — tracked by the `hosted_backend` plan), and
sys-gui-007's disk lane.

## Dependencies

- **sys-gui-006 bare desktop** — must reach LIVE-GREEN
  (`doc/08_tracking/todo/sys_gui_006_bare_desktop_resume_2026-04-14.md`).
  The framebuffer lane is the reference scene SYS-GUI-008 diffs
  against; without a committed `desktop_scene.ppm` there is no
  baseline to compare the virtio-gpu output to.
- **sys-gui-006 with-apps** — should also be green
  (`doc/08_tracking/todo/sys_gui_006_with_apps_resume_2026-04-14.md`)
  so the multi-window scene under test exercises the compositor, not
  just a single flood-fill.
- **sys-gui-007** (disk lane) — NOT a blocker. Independent lane.
  Currently blocked on Architecture enum regressions per its
  resume checklist.
- **`gui_layer_contract.md` Row 1** — already locked upstream
  (plan Section 4 Row 1). No work.
- **Compiler blockers from sys-gui-006 Round 8** — parser/spec load
  fixes must have landed so `test/system/` specs run live.

## Current state snapshot

- Driver: `src/os/drivers/virtio/virtio_gpu.spl` — full legacy-PCI
  transport, controlq wired, `flush` / `flush_rect` / resource
  management implemented; DMA via syscall 84, BAR0 via syscall 83.
- Driver: `src/os/drivers/gpu/virtio_gpu_entry.spl:1` (162 lines) —
  standalone smoke entry. Boots, scans PCI, draws test pattern,
  flushes. Runs under scenario `x64-gpu-2d`.
- Driver: `src/os/drivers/gpu/gpu_accel.spl:1` — module-level
  `gpu_accel_supported` flag + `glass_render.c` extern mirror
  (`rt_gui_set_gpu_mode` / `rt_gui_take_pending_flush`).
- Engine2D backend: `src/lib/gc_async_mut/gpu/engine2d/backend_virtio_gpu.spl:1`
  (440 lines). `create` (L55), `name` (L76), `init` (L79),
  `shutdown` (L99), `read_pixels` (L322), `width/height` (L330/L333),
  internal pixel/line/arc/edge helpers L340–L439. Implemented; no
  `unreachable!` markers. Shares glyph module with other backends.
- Compositor: `src/os/compositor/display_backend.spl:1` — trait at
  top; `FbCompositorBackend` L76+, `GpuCompositorBackend` L150;
  impl at L161 wires `present()` → `gpu.flush()` (L215) and
  `present_rect()` → `gpu.flush_rect(...)` (L219); factory
  `GpuCompositorBackend.new` at L243–L247.
- Entry: `examples/simple_os/arch/x86_64/gui_entry_engine2d_virtio.spl:1`
  (150 lines) — proves Engine2D-over-virtio-gpu boot path. Halts
  before compositor hand-off; note in header calls this out as the
  follow-up SYS-GUI-008 must finish.
- QEMU scenario: `src/os/qemu_runner.spl:827` `scenario_x64_gpu_2d()`
  already defined; `qemu_extra` includes
  `-device virtio-gpu,disable-modern=on,disable-legacy=off -vga none`.
- Tests: `test/system/simpleos_desktop_framebuffer_spec.spl` exists
  for the BGA lane. NO sys-gui-008 test spec, NO virtio baseline
  directory exists yet on origin/main. No `sys-gui-008` / `sys_gui_008`
  references found anywhere except Row 4 of the plan and
  `doc/04_architecture/cross_platform_wm.md:355`.

## Target state

- `test/system/simpleos_desktop_virtio_gpu_spec.spl` green in both
  prerun and live lanes; ≤1% perceptual diff against the
  sys-gui-006 framebuffer baseline.
- `test/baselines/simpleos_desktop_virtio_gpu/desktop_scene.ppm`
  committed (real scanout pull, not synthetic).
- `gui_entry_engine2d_virtio.spl` extended past the "halt before
  hand-off" point to install `GpuCompositorBackend` under the
  real compositor and drive `os/desktop/shell.spl`.
- QEMU boots `scenario_x64_gpu_2d` + the desktop kernel and reaches
  a `[desktop-e2e] desktop-ready` marker identical to sys-gui-006.
- `wm_compare` (Row 2 of the plan) can diff V1-framebuffer vs.
  V1-virtio-gpu and produce a parity report.
- Headless CI run supported (QEMU `-display none` + scanout capture
  via `flush_rect` buffer readback, not host display).

## Round milestones

- **Round 0 — Compositor hand-off in the virtio entry.**
  Extend `examples/simple_os/arch/x86_64/gui_entry_engine2d_virtio.spl`
  past the halt: construct `GpuCompositorBackend.new(gpu)`, install
  it as the compositor backend, and reach the `desktop-ready` marker
  on a blank scene. Artifact: scenario `x64-gpu-2d` boot log
  containing `desktop-ready`.
- **Round 1 — System spec skeleton.**
  Add `test/system/simpleos_desktop_virtio_gpu_spec.spl` mirroring
  `simpleos_desktop_framebuffer_spec.spl`: profile, markers, skip
  paths, zero-byte placeholder PPM. Self-heal path on
  `UPDATE_BASELINE=1`. Artifact: spec file + placeholder PPM + README.
- **Round 2 — Scanout capture.**
  Implement a `VirtioGpuDriver.dump_scanout()` (or reuse
  `read_pixels`) that writes a host-visible PPM after the compositor's
  final flush. Artifact: committed non-zero
  `test/baselines/simpleos_desktop_virtio_gpu/desktop_scene.ppm`.
- **Round 3 — Parity gate.**
  Wire the spec to diff against sys-gui-006's PPM at ≤1%
  perceptual difference using the same diff harness Row 8 uses.
  Artifact: spec passes prerun and live, diff report in test log.
- **Round 4 — wm_compare integration.**
  Teach `src/app/wm_compare/` to treat `virtio-gpu` as a third lane
  alongside framebuffer and hosted, using
  `test/sys/wm_compare/v1_v2_parity_spec.spl` as template. Artifact:
  `v1_fb_vs_v1_gpu_parity_spec.spl` green.
- **Round 5 — Headless CI lock.**
  Run the spec under `-display none` with scanout readback, verify
  RSS + wall-clock budgets, and add the scenario to the default
  system-test set. Artifact: green CI run + updated
  `doc/06_spec/app/compiler/feature/windows_spec.md` row.

## Entry wiring

Mirror sys-gui-006: dispatch by **QEMU scenario name**, not a
compile-time flag. The existing entries already split by purpose
(`gui_entry_engine2d.spl` for BGA, `gui_entry_engine2d_virtio.spl`
for virtio). sys-gui-008 picks the virtio entry when the scenario is
`x64-gpu-2d` (`src/os/qemu_runner.spl:827`); the framebuffer lane
stays on `x64-desktop-test` (`qemu_runner.spl:927`). Runtime PCI
probe inside the virtio entry already gates on device presence and
falls through to a serial-logged halt if absent — no env var needed.
The `gpu_accel_supported` flag in `src/os/drivers/gpu/gpu_accel.spl`
stays as the C-side mirror so `glass_render.c` suppresses the MMIO
memcpy fallback.

## Acceptance criteria

- `test/system/simpleos_desktop_virtio_gpu_spec.spl` passes in
  prerun and live lanes.
- Scene diff vs. `simpleos_desktop_framebuffer/desktop_scene.ppm`
  ≤1% perceptual pixels changed.
- `gui_entry_engine2d_virtio.spl` emits `[desktop-e2e] desktop-ready`
  under scenario `x64-gpu-2d`.
- `VirtioGpuBackend.name()` returns `"virtio-gpu"` at the runtime
  assert gate (already true at L76 — must stay).
- Spec hard-fails if `[desktop-ready]` marker missing
  (regression gate mirrors sys-gui-006's contract).
- Scenario runs under `-display none` with scanout readback; wall
  clock ≤ framebuffer lane + 50%.
- `wm_compare` parity lane green in round 4.
- No stray `unreachable!` or `TODO` introduced in
  `backend_virtio_gpu.spl` / `display_backend.spl` / the entry.

## Risks

- virtio-gpu legacy PCI command-stream correctness: `flush_rect`
  packs (x1,y1,x2,y2) as u16 halves; off-by-one at the scanout edge
  would silently shift the diff >1%. Mitigate with per-rect unit
  tests before the full-scene diff.
- QEMU 8.2.2 `-vga none -device virtio-gpu` quirks: some builds
  require `virtio-vga-gl` for scanout visibility; CI must pin the
  exact QEMU invocation from `scenario_x64_gpu_2d`.
- Headless scanout readback: `read_pixels` returns the Simple-side
  local buffer, not the host-visible scanout. Round 2 must decide
  whether to diff the local buffer (fast, misses driver bugs) or
  pull via virtio-gpu `GET_CAPSET` / resource readback (slow, real).
- DMA timing under isa-debug-exit: guest may exit before the last
  controlq response lands; need a flush-barrier before `halt_forever`.
- `gpu_accel_supported` double-path with `glass_render.c`: if the
  C mirror is stale the MMIO fallback fires alongside virtio flush
  and corrupts the diff.

## Open questions

- Is the scanout readback for CI diff done via Simple-side
  `read_pixels` or an actual virtio-gpu readback command? Affects
  whether the gate catches driver-level regressions.
- Should `gui_entry_engine2d_virtio.spl` be extended in place, or
  forked into a new `gui_entry_desktop_virtio.spl` to keep the
  smoke-only entry untouched?
- Does `wm_compare` need a third lane type or can it reuse the V1
  slot with a backend-variant tag?
- Do we keep `scenario_x64_gpu_2d` alongside a new
  `scenario_x64_desktop_gpu` (mirroring `x64-desktop-test` vs
  `x64-gpu-2d`), or overload the existing scenario?
- Text rendering lane: `GpuCompositorBackend.draw_text` at
  `display_backend.spl:177` loops over `draw_char_8x16`. Does this
  match the framebuffer lane's glyph choice closely enough for the
  1% gate, or do we need a shared glyph snapshot first?
