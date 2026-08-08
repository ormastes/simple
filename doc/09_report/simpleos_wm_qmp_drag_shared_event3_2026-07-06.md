# SimpleOS WM QMP Drag Delta Evidence

- status: pass
- reason: pass
- simple bin: /Users/ormastes/simple/bin/release/aarch64-apple-darwin-macho/simple
- simple bin source: self-hosted:/Users/ormastes/simple/bin/release/aarch64-apple-darwin-macho/simple
- simple bin status: pass
- launcher status: pass
- launcher reason: pass
- launcher target: wm-simple-web
- launcher entry: examples/09_embedded/simple_os/arch/x86_64/gui_entry_engine2d.spl
- qmp socket: /tmp/simpleos_desktop_qmp_8461_1783323571777285.sock
- marker state: probe:true wm:true engine:true web:true mdi:true top:true taskbar:true html:true
- injection protocol: hmp-mouse-events
- guest input contract: pass (pass)
- guest mouse polling: pass
- guest keyboard polling: pass
- guest shared pointer event: pass (pass)
- changed bytes: 149734
- source region changed pixels: 14680
- target region changed pixels: 8234
- before sha256: f6fe8418ef48288cbfbe44de7030d8f086091f0985629268bbf4368c6ca91979
- after sha256: d51a0e81f3c97795c6ed61fc52038fa557a66f45f4f94e06fb622465ba0ea374
- before ppm: build/simpleos_wm_qmp_drag_shared_event3_2026_07_06/before-drag.ppm (2359312 bytes)
- before raw: build/simpleos_wm_qmp_drag_shared_event3_2026_07_06/before-drag.ppm.raw (3145728 bytes; pass)
- before ppm status: pass; magic pass
- after ppm: build/simpleos_wm_qmp_drag_shared_event3_2026_07_06/after-drag.ppm (2359312 bytes)
- after raw: build/simpleos_wm_qmp_drag_shared_event3_2026_07_06/after-drag.ppm.raw (3145728 bytes; pass)
- after ppm status: pass; magic pass
- serial log: build/os/simpleos_desktop_qmp_8461_1783323571777285.log (2908 bytes)
- stderr log: build/os/simpleos_desktop_qmp_8461_1783323571777285.log.stderr (0 bytes)

This wrapper launches the exact WM + Simple Web + Engine2D target in a
separate QEMU process, captures the BGA framebuffer with QMP
`pmemsave`, injects HMP `mouse_move` / `mouse_button` events, and
requires both global byte changes and drag-region-local changes. It does
not use blur, downscaling, tolerance matching, or copied reference pixels.
