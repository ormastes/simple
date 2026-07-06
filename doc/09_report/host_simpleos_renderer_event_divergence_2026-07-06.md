<!-- codex-architecture -->
# Host/SimpleOS Renderer and Event Divergence

Date: 2026-07-06
Owner: Worker 2 docs/tests evidence lane
Sidecars: N/A - concise evidence consolidation only
Merge owner: current Worker 2
Final reviewer: normal/highest-capability reviewer

## Status

Host and SimpleOS now converge at the intended architecture boundary: shared WM
layout, chrome, MDI surface data, framebuffer rendering, and drag lifecycle
events flow through the shared renderer/event abstractions. Host-only cached web
pixel rendering remains an adapter effect; SimpleOS/QEMU presents through the
framebuffer backend and must not depend on host file/env/runtime render queues.

## Evidence Assertions

- Visible SimpleOS/QEMU display-surface evidence exists in
  `doc/09_report/simpleos_wm_shared_renderer_fullscreen_opt_2026-07-06.md`:
  serial markers include `renderer=shared_mdi_framebuffer_scene`,
  `source=shared_mdi_framebuffer_scene`, `direct-mmio-commit`, and browser
  `html-renderable` pixel/checksum evidence, with QMP `pmemsave` framebuffer
  captures for fullscreen and restored states.
- Drag/event evidence exists in
  `doc/09_report/simpleos_wm_qmp_drag_shared_event3_2026-07-06.md`: the run
  records HMP mouse injection, guest mouse and keyboard polling, a decoded mouse
  packet, `qemu-shared-pointer-event source=wm_lifecycle_pointer_move`, and
  before/after QMP framebuffer deltas.
- The low-risk spec guard in
  `test/01_unit/os/compositor/shared_mdi_framebuffer_scene_spec.spl` now asserts
  that the x86_64 QEMU entry advertises both shared display-surface evidence
  markers and PS/2 mouse demux markers, without editing runtime source.

## Remaining Divergence

- Host rich web content can still use cached host pixel artifacts below the
  adapter boundary; SimpleOS/QEMU stays on direct framebuffer presentation.
- PS/2 demux evidence is stronger, but the demux code is still x86_64 QEMU
  entry-local. The shared event boundary is the lifecycle conversion into
  `wm_lifecycle_pointer_move`.
- Direct-MMIO performance work remains tracked separately in
  `doc/08_tracking/bug/shared_wm_qemu_direct_mmio_backend_perf_2026-07-06.md`.
