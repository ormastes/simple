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
- qmp socket: /tmp/simpleos_desktop_qmp_95666_1783327988308775.sock
- marker state: probe:true wm:true engine:true web:true mdi:true top:true taskbar:true html:true
- injection protocol: hmp-mouse-events
- guest input contract: pass (pass)
- guest mouse polling: pass
- guest keyboard polling: pass
- guest shared pointer event: pass (pass)
- guest decoded mouse packet: pass (pass)
- changed bytes: 149734
- source region changed pixels: 14680
- target region changed pixels: 8234
- before sha256: 4fe2c350f4b62c029fd9f0504b8d455be423bd8230fb62f1454b6076458a1b77
- after sha256: 715baa3940310e70ea1579a80a4233a94d840c452e3fd421aa66d56eb0204a62
- before ppm: build/simpleos_wm_drag_sanity_aux_2026_07_06/before-drag.ppm (2359312 bytes)
- before raw: build/simpleos_wm_drag_sanity_aux_2026_07_06/before-drag.ppm.raw (3145728 bytes; pass)
- before ppm status: pass; magic pass
- after ppm: build/simpleos_wm_drag_sanity_aux_2026_07_06/after-drag.ppm (2359312 bytes)
- after raw: build/simpleos_wm_drag_sanity_aux_2026_07_06/after-drag.ppm.raw (3145728 bytes; pass)
- after ppm status: pass; magic pass
- serial log: build/os/simpleos_desktop_qmp_95666_1783327988308775.log (2987 bytes)
- stderr log: build/os/simpleos_desktop_qmp_95666_1783327988308775.log.stderr (0 bytes)

This wrapper launches the exact WM + Simple Web + Engine2D target in a
separate QEMU process, captures the BGA framebuffer with QMP
`pmemsave`, injects HMP `mouse_move` / `mouse_button` events, and
requires both global byte changes and drag-region-local changes. It does
not use blur, downscaling, tolerance matching, or copied reference pixels.
