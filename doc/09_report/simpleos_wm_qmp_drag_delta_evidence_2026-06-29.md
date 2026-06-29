# SimpleOS WM QMP Drag Delta Evidence

- status: fail
- reason: guest-entry-keyboard-only-for-mouse-injection
- simple bin: /home/yoon/simple/release/x86_64-unknown-linux-gnu/simple
- simple bin source: self-hosted:/home/yoon/simple/release/x86_64-unknown-linux-gnu/simple
- simple bin status: pass
- launcher status: pass
- launcher reason: pass
- launcher target: wm-simple-web
- launcher entry: examples/09_embedded/simple_os/arch/x86_64/gui_entry_engine2d.spl
- qmp socket: /tmp/simpleos_desktop_qmp_1868319_1782707647168573832.sock
- marker state: probe:true wm:true engine:true web:true mdi:true top:true taskbar:true html:true
- injection protocol: hmp-mouse-events
- guest input contract: fail (guest-entry-keyboard-only-for-mouse-injection)
- guest mouse polling: missing
- guest keyboard polling: pass
- changed bytes: 0
- source region changed pixels: 0
- target region changed pixels: 0
- before sha256: 5fcc2dc196224169bc9a044e57bd2faa88f4ff3dddf415f6d4b44e805d2d1f8f
- after sha256: 5fcc2dc196224169bc9a044e57bd2faa88f4ff3dddf415f6d4b44e805d2d1f8f
- before ppm: build/simpleos_wm_qmp_drag_delta_evidence/before-drag.ppm (2359312 bytes)
- before raw: build/simpleos_wm_qmp_drag_delta_evidence/before-drag.ppm.raw (3145728 bytes; pass)
- before ppm status: pass; magic pass
- after ppm: build/simpleos_wm_qmp_drag_delta_evidence/after-drag.ppm (2359312 bytes)
- after raw: build/simpleos_wm_qmp_drag_delta_evidence/after-drag.ppm.raw (3145728 bytes; pass)
- after ppm status: pass; magic pass
- serial log: build/os/simpleos_desktop_qmp_1868319_1782707647168573832.log (1285 bytes)
- stderr log: build/os/simpleos_desktop_qmp_1868319_1782707647168573832.log.stderr (0 bytes)

This wrapper launches the exact WM + Simple Web + Engine2D target in a
separate QEMU process, captures the BGA framebuffer with QMP
`pmemsave`, injects HMP `mouse_move` / `mouse_button` events, and
requires both global byte changes and drag-region-local changes. It does
not use blur, downscaling, tolerance matching, or copied reference pixels.
