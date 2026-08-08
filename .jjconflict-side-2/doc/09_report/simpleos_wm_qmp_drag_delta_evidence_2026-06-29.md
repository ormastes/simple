# SimpleOS WM QMP Drag Delta Evidence

- status: pass
- reason: pass
- simple bin: /home/yoon/simple/bin/release/x86_64-unknown-linux-gnu/simple
- simple bin source: self-hosted:/home/yoon/simple/bin/release/x86_64-unknown-linux-gnu/simple
- simple bin status: pass
- launcher status: pass
- launcher reason: pass
- launcher target: wm-simple-web
- launcher entry: examples/09_embedded/simple_os/arch/x86_64/gui_entry_engine2d.spl
- qmp socket: /tmp/simpleos_desktop_qmp_3311078_1782749592571413948.sock
- marker state: probe:true wm:true engine:true web:true mdi:true top:true taskbar:true html:true
- injection protocol: hmp-mouse-events
- guest input contract: pass (pass)
- guest mouse polling: pass
- guest keyboard polling: pass
- changed bytes: 376700
- source region changed pixels: 9300
- target region changed pixels: 1120
- before sha256: 5fcc2dc196224169bc9a044e57bd2faa88f4ff3dddf415f6d4b44e805d2d1f8f
- after sha256: c33b92bbeaee5f6ec9ce288b61b20448bcb85fc76f0d9cb985e2d8328376a2e1
- before ppm: build/simpleos_wm_qmp_drag_delta_evidence/before-drag.ppm (2359312 bytes)
- before raw: build/simpleos_wm_qmp_drag_delta_evidence/before-drag.ppm.raw (3145728 bytes; pass)
- before ppm status: pass; magic pass
- after ppm: build/simpleos_wm_qmp_drag_delta_evidence/after-drag.ppm (2359312 bytes)
- after raw: build/simpleos_wm_qmp_drag_delta_evidence/after-drag.ppm.raw (3145728 bytes; pass)
- after ppm status: pass; magic pass
- serial log: build/os/simpleos_desktop_qmp_3311078_1782749592571413948.log (1494 bytes)
- stderr log: build/os/simpleos_desktop_qmp_3311078_1782749592571413948.log.stderr (0 bytes)

This wrapper launches the exact WM + Simple Web + Engine2D target in a
separate QEMU process, captures the BGA framebuffer with QMP
`pmemsave`, injects HMP `mouse_move` / `mouse_button` events, and
requires both global byte changes and drag-region-local changes. It does
not use blur, downscaling, tolerance matching, or copied reference pixels.
