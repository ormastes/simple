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
- qmp socket: /tmp/simpleos_desktop_qmp_95980_1783319793375185.sock
- marker state: probe:true wm:true engine:true web:true mdi:true top:true taskbar:true html:true
- injection protocol: hmp-mouse-events
- guest input contract: pass (pass)
- guest mouse polling: pass
- guest keyboard polling: pass
- changed bytes: 321972
- source region changed pixels: 15000
- target region changed pixels: 23400
- before sha256: fe59dff4f3bf54bb26946fc11802fffddfe388c4b37183e1810a8683e89f338c
- after sha256: 884b55ee561cc43bf269b2b02e8617a82ded5a288914f614c2f362bb0137cc50
- before ppm: build/simpleos_wm_qmp_drag_goal_2026_07_06/before-drag.ppm (2359312 bytes)
- before raw: build/simpleos_wm_qmp_drag_goal_2026_07_06/before-drag.ppm.raw (3145728 bytes; pass)
- before ppm status: pass; magic pass
- after ppm: build/simpleos_wm_qmp_drag_goal_2026_07_06/after-drag.ppm (2359312 bytes)
- after raw: build/simpleos_wm_qmp_drag_goal_2026_07_06/after-drag.ppm.raw (3145728 bytes; pass)
- after ppm status: pass; magic pass
- serial log: build/os/simpleos_desktop_qmp_95980_1783319793375185.log (1739 bytes)
- stderr log: build/os/simpleos_desktop_qmp_95980_1783319793375185.log.stderr (0 bytes)

This wrapper launches the exact WM + Simple Web + Engine2D target in a
separate QEMU process, captures the BGA framebuffer with QMP
`pmemsave`, injects HMP `mouse_move` / `mouse_button` events, and
requires both global byte changes and drag-region-local changes. It does
not use blur, downscaling, tolerance matching, or copied reference pixels.
