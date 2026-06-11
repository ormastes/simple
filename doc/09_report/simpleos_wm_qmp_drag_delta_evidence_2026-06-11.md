# SimpleOS WM QMP Drag Delta Evidence

- status: unavailable
- reason: wm-qmp-launch-failed
- launcher status: 
- launcher reason: 
- launcher target: 
- launcher entry: 
- qmp socket: -
- marker state: -
- changed bytes: 0
- source region changed pixels: 0
- target region changed pixels: 0
- before sha256: -
- after sha256: -
- before ppm: build/simpleos_wm_qmp_drag_delta_evidence/before-drag.ppm (0 bytes)
- after ppm: build/simpleos_wm_qmp_drag_delta_evidence/after-drag.ppm (0 bytes)
- serial log: - (0 bytes)
- stderr log: - (0 bytes)

Follow-up on 2026-06-11:

- Restored historical `gui_entry_engine2d.spl` and `wm_input_test_entry.spl`
  entries type-check with the current compiler inside the isolated repair
  worktree. They were not committed to the superproject because current
  `origin/main` records `examples/09_embedded/simple_os` as a gitlink.
- The focused launcher still exits `139` before structured launcher fields are
  emitted; `launch.out` contains only `Segmentation fault (core dumped)`.
- Direct source rebuild is still not available. The target metadata names
  `examples/09_embedded/simple_os/arch/x86_64/linker.ld`, which is absent. Using
  the current `src/os/kernel/arch/x86_64/linker.ld` instead reaches the linker
  but fails on unresolved freestanding runtime symbols including
  `rt_string_new`, `rt_port_outb`, `serial_println`, and `rt_mmio_read_u32`.

This wrapper launches the exact WM + Simple Web + Engine2D target in a
separate QEMU process, captures the BGA framebuffer with QMP
`pmemsave`, injects HMP `mouse_move` / `mouse_button` events, and
requires both global byte changes and drag-region-local changes. It does
not use blur, downscaling, tolerance matching, or copied reference pixels.
