# SimpleOS WM QMP Drag Delta Evidence

- status: fail
- reason: qmp-drag-delta-not-proven
- launcher status: pass
- launcher reason: pass
- launcher target: wm-simple-web
- launcher entry: examples/09_embedded/simple_os/arch/x86_64/gui_entry_engine2d.spl
- qmp socket: /tmp/simpleos_desktop_qmp_636264_1781167738273354417.sock
- marker state: probe:true wm:true engine:true web:true mdi:true top:true taskbar:true html:true
- changed bytes: 0
- source region changed pixels: 0
- target region changed pixels: 0
- before sha256: 5fcc2dc196224169bc9a044e57bd2faa88f4ff3dddf415f6d4b44e805d2d1f8f
- after sha256: 5fcc2dc196224169bc9a044e57bd2faa88f4ff3dddf415f6d4b44e805d2d1f8f
- before ppm: build/matrix_input_send/before-drag.ppm (2359312 bytes)
- after ppm: build/matrix_input_send/after-drag.ppm (2359312 bytes)
- serial log: build/os/simpleos_desktop_qmp_636264_1781167738273354417.log (1368 bytes)
- stderr log: build/os/simpleos_desktop_qmp_636264_1781167738273354417.log.stderr (50 bytes)

This wrapper launches the exact WM + Simple Web + Engine2D target in a
separate QEMU process, captures the BGA framebuffer with QMP
`pmemsave`, injects HMP `mouse_move` / `mouse_button` events, and
requires both global byte changes and drag-region-local changes. It does
not use blur, downscaling, tolerance matching, or copied reference pixels.

The current `simple_os` submodule initializes PS/2 auxiliary mouse reporting
inside `gui_entry_engine2d.spl` and waits after `render-ready` for real 3-byte
PS/2 mouse packets before re-rendering the browser window at a new position. The
guest reports `[host-input] no-host-mouse-packets`, so this remains a real
failure rather than a relaxed or synthetic pass.

Additional host-input matrix on 2026-06-11:

- QEMU `q35` + HMP `mouse_move`/`mouse_button`: no PS/2 aux packets.
- QEMU `pc` + HMP `mouse_move`/`mouse_button`: no PS/2 aux packets.
- QEMU `q35` + QMP `input-send-event` relative/button events: no PS/2 aux
  packets.

All variants kept the same strict framebuffer gate and produced
`changed_bytes=0`.
