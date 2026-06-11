# SimpleOS WM QMP Drag Delta Evidence

- status: unavailable
- reason: wm-simple-web-source-missing
- launcher status: unavailable
- launcher reason: wm-simple-web-source-missing
- launcher target: wm-simple-web
- launcher entry: examples/09_embedded/simple_os/arch/x86_64/gui_entry_engine2d.spl
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

This wrapper launches the exact WM + Simple Web + Engine2D target in a
separate QEMU process, captures the BGA framebuffer with QMP
`pmemsave`, injects HMP `mouse_move` / `mouse_button` events, and
requires both global byte changes and drag-region-local changes. It does
not use blur, downscaling, tolerance matching, or copied reference pixels.
