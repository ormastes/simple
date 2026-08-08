# SimpleOS WM QMP Drag Delta Evidence

- status: fail
- reason: qmp-drag-delta-not-proven
- simple bin: /Users/ormastes/simple/bin/release/aarch64-apple-darwin-macho/simple
- simple bin source: self-hosted:/Users/ormastes/simple/bin/release/aarch64-apple-darwin-macho/simple
- simple bin status: pass
- launcher status: pass
- launcher reason: pass
- launcher target: wm-simple-web
- launcher entry: examples/09_embedded/simple_os/arch/x86_64/gui_entry_engine2d.spl
- qmp socket: /tmp/simpleos_desktop_qmp_82127_1783323503950865.sock
- marker state: probe:true wm:true engine:true web:true mdi:true top:true taskbar:true html:true
- injection protocol: hmp-mouse-events
- guest input contract: pass (pass)
- guest mouse polling: pass
- guest keyboard polling: pass
- guest shared pointer event: pass (pass)
- changed bytes: 558
- source region changed pixels: 0
- target region changed pixels: 186
- before sha256: 6b705ce5ac15b4346556bde5a8ac7f30cf1bbe1fcbf66acf91a68cdb2d21249c
- after sha256: 98ec878c8b570fabfa02850f51dacade2194f69408e26f21ce243063c9d51b2c
- before ppm: build/simpleos_wm_qmp_drag_shared_event2_2026_07_06/before-drag.ppm (2359312 bytes)
- before raw: build/simpleos_wm_qmp_drag_shared_event2_2026_07_06/before-drag.ppm.raw (3145728 bytes; pass)
- before ppm status: pass; magic pass
- after ppm: build/simpleos_wm_qmp_drag_shared_event2_2026_07_06/after-drag.ppm (2359312 bytes)
- after raw: build/simpleos_wm_qmp_drag_shared_event2_2026_07_06/after-drag.ppm.raw (3145728 bytes; pass)
- after ppm status: pass; magic pass
- serial log: build/os/simpleos_desktop_qmp_82127_1783323503950865.log (19735 bytes)
- stderr log: build/os/simpleos_desktop_qmp_82127_1783323503950865.log.stderr (0 bytes)

This wrapper launches the exact WM + Simple Web + Engine2D target in a
separate QEMU process, captures the BGA framebuffer with QMP
`pmemsave`, injects HMP `mouse_move` / `mouse_button` events, and
requires both global byte changes and drag-region-local changes. It does
not use blur, downscaling, tolerance matching, or copied reference pixels.
