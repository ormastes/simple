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
- qmp socket: /tmp/simpleos_desktop_qmp_13415_1783320175379193.sock
- marker state: probe:true wm:true engine:true web:true mdi:true top:true taskbar:true html:true
- injection protocol: hmp-mouse-events
- guest input contract: pass (pass)
- guest mouse polling: pass
- guest keyboard polling: pass
- changed bytes: 416685
- source region changed pixels: 15000
- target region changed pixels: 23400
- before sha256: fe59dff4f3bf54bb26946fc11802fffddfe388c4b37183e1810a8683e89f338c
- after sha256: aeac4e210908e6877ae0492838c5db3d0dd74ae6474e77a47564505d06fbdc00
- before ppm: build/qemu_parallel_drag_2026_07_06/before-drag.ppm (2359312 bytes)
- before raw: build/qemu_parallel_drag_2026_07_06/before-drag.ppm.raw (3145728 bytes; pass)
- before ppm status: pass; magic pass
- after ppm: build/qemu_parallel_drag_2026_07_06/after-drag.ppm (2359312 bytes)
- after raw: build/qemu_parallel_drag_2026_07_06/after-drag.ppm.raw (3145728 bytes; pass)
- after ppm status: pass; magic pass
- serial log: build/os/simpleos_desktop_qmp_13415_1783320175379193.log (1776 bytes)
- stderr log: build/os/simpleos_desktop_qmp_13415_1783320175379193.log.stderr (0 bytes)

This wrapper launches the exact WM + Simple Web + Engine2D target in a
separate QEMU process, captures the BGA framebuffer with QMP
`pmemsave`, injects HMP `mouse_move` / `mouse_button` events, and
requires both global byte changes and drag-region-local changes. It does
not use blur, downscaling, tolerance matching, or copied reference pixels.
