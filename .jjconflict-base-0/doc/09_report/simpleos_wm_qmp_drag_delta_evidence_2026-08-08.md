# SimpleOS WM QMP Drag Delta Evidence

- status: unavailable
- reason: wm-qmp-launch-failed
- simple bin: /home/ormastes/dev/pub/simple/bin/release/aarch64-unknown-simpleos/simple
- simple bin source: self-hosted:/home/ormastes/dev/pub/simple/bin/release/aarch64-unknown-simpleos/simple
- simple bin status: pass
- launcher status: 
- launcher reason: 
- launcher target: 
- launcher entry: 
- qmp socket: -
- marker state: -
- injection protocol: hmp-mouse-events
- guest input contract: fail (guest-entry-not-reported)
- guest mouse polling: missing
- guest keyboard polling: missing
- guest shared pointer event: not-run (not-run)
- guest decoded mouse packet: not-run (not-run)
- guest geometry receipt: not-run (not-run)
- guest geometry: -,- -> -,-
- framebuffer delta: not-run (not-run)
- event evidence: not-run (not-run)
- changed bytes: 0
- source region changed pixels: 0
- target region changed pixels: 0
- before sha256: -
- after sha256: -
- drag receipt elapsed ms: 0
- before ppm: build/simpleos_wm_qmp_drag_delta_evidence/before-drag.ppm (0 bytes)
- before raw: build/simpleos_wm_qmp_drag_delta_evidence/before-drag.ppm.raw (0 bytes; missing)
- before ppm status: missing; magic missing
- after ppm: build/simpleos_wm_qmp_drag_delta_evidence/after-drag.ppm (0 bytes)
- after raw: build/simpleos_wm_qmp_drag_delta_evidence/after-drag.ppm.raw (0 bytes; missing)
- after ppm status: missing; magic missing
- serial log: - (0 bytes)
- stderr log: - (0 bytes)

This wrapper launches the exact WM + Simple Web + Engine2D target in a
separate QEMU process, captures the BGA framebuffer with QMP
`pmemsave`, injects HMP `mouse_move` / `mouse_button` events, and
requires both global byte changes and drag-region-local changes. It does
not use blur, downscaling, tolerance matching, or copied reference pixels.
