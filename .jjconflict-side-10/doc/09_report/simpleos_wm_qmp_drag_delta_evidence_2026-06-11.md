# SimpleOS WM QMP Drag Delta Evidence

- status: fail
- reason: qmp-drag-delta-not-proven
- launcher status: pass
- launcher reason: pass
- launcher target: wm-simple-web
- launcher entry: examples/09_embedded/simple_os/arch/x86_64/gui_entry_engine2d.spl
- qmp socket: /tmp/simpleos_desktop_qmp_645603_1781168144797769588.sock
- marker state: probe:true wm:true engine:true web:true mdi:true top:true taskbar:true html:true
- changed bytes: 0
- source region changed pixels: 0
- target region changed pixels: 0
- before sha256: 5fcc2dc196224169bc9a044e57bd2faa88f4ff3dddf415f6d4b44e805d2d1f8f
- after sha256: 5fcc2dc196224169bc9a044e57bd2faa88f4ff3dddf415f6d4b44e805d2d1f8f
- before ppm: build/wm_timing_extended/before-drag.ppm (2359312 bytes)
- after ppm: build/wm_timing_extended/after-drag.ppm (2359312 bytes)
- serial log: build/os/simpleos_desktop_qmp_645603_1781168144797769588.log (1364 bytes)
- stderr log: build/os/simpleos_desktop_qmp_645603_1781168144797769588.log.stderr (50 bytes)

This wrapper launches the exact WM + Simple Web + Engine2D target in a
separate QEMU process, captures the BGA framebuffer with QMP
`pmemsave`, injects HMP `mouse_move` / `mouse_button` events, and
requires both global byte changes and drag-region-local changes. It does
not use blur, downscaling, tolerance matching, or copied reference pixels.

The current `simple_os` submodule initializes PS/2 auxiliary mouse reporting
inside `gui_entry_engine2d.spl` and waits after `render-ready` for real 3-byte
PS/2 mouse packets before re-rendering the browser window at a new position.
This timing run extended the guest polling window and emitted
`[host-input] poll-window-start` before the wrapper injected host pointer
events. The serial log did not reach `[host-input] poll-window-end` before the
after-frame capture, so host injection happened while the guest was still
polling. The framebuffer hashes remained identical and `changed_bytes=0`, so
this remains a real failure rather than a relaxed or synthetic pass.

Additional host-input matrix on 2026-06-11:

- QEMU `q35` + HMP `mouse_move`/`mouse_button`: no PS/2 aux packets.
- QEMU `pc` + HMP `mouse_move`/`mouse_button`: no PS/2 aux packets.
- QEMU `q35` + QMP `input-send-event` relative/button events: no PS/2 aux
  packets.
- QEMU `q35` + HMP with extended guest poll window: poll window active,
  `changed_bytes=0`.

All variants kept the same strict framebuffer gate and produced no proven drag
delta.
