# SimpleOS WM QMP Drag Delta Evidence

- status: pass
- reason: pass
- simple bin: bin/simple
- simple bin source: explicit-env
- simple bin status: pass
- launcher status: pass
- launcher reason: pass
- launcher target: wm-simple-web
- launcher entry: examples/09_embedded/simple_os/arch/x86_64/gui_entry_engine2d.spl
- qmp socket: /tmp/simpleos_desktop_qmp_17060_1783341865355198.sock
- marker state: probe:true wm:true engine:true web:true mdi:true top:true taskbar:true html:true
- injection protocol: hmp-mouse-events
- guest input contract: pass (pass)
- guest mouse polling: pass
- guest keyboard polling: pass
- guest shared pointer event: pass (pass)
- guest decoded mouse packet: pass (pass)
- framebuffer delta: pass (pass)
- event evidence: pass (pass)
- changed bytes: 157660
- source region changed pixels: 14686
- target region changed pixels: 9682
- before sha256: dc595bb2ef53d2516faa2dc8ca72577e3ec590584544e69d4de66d884eade0cc
- after sha256: 0647ffeef4dc7c42d815b77849baff6cc3b0fe7b70e025bf6c0d53f86cfda567
- before ppm: build/simpleos_wm_qmp_drag_delta_gui_renderer/before-drag.ppm (2359312 bytes)
- before raw: build/simpleos_wm_qmp_drag_delta_gui_renderer/before-drag.ppm.raw (3145728 bytes; pass)
- before ppm status: pass; magic pass
- after ppm: build/simpleos_wm_qmp_drag_delta_gui_renderer/after-drag.ppm (2359312 bytes)
- after raw: build/simpleos_wm_qmp_drag_delta_gui_renderer/after-drag.ppm.raw (3145728 bytes; pass)
- after ppm status: pass; magic pass
- serial log: build/os/simpleos_desktop_qmp_17060_1783341865355198.log (1607 bytes)
- stderr log: build/os/simpleos_desktop_qmp_17060_1783341865355198.log.stderr (0 bytes)

This wrapper launches the exact WM + Simple Web + Engine2D target in a
separate QEMU process, captures the BGA framebuffer with QMP
`pmemsave`, injects HMP `mouse_move` / `mouse_button` events, and
requires both global byte changes and drag-region-local changes. It does
not use blur, downscaling, tolerance matching, or copied reference pixels.
