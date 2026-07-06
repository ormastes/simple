# SimpleOS WM Fullscreen Evidence

- status: unavailable
- reason: fullscreen-enter-marker-missing
- simple bin: /Users/ormastes/simple/bin/release/aarch64-apple-darwin-macho/simple
- simple bin source: self-hosted:/Users/ormastes/simple/bin/release/aarch64-apple-darwin-macho/simple
- simple bin status: pass
- qmp socket: build/qemu_shared_renderer_fullscreen_2026_07_06/qmp.sock
- fullscreen-enter marker: -
- fullscreen-exit marker: -
- fullscreen size: - (width=0 height=0)
- changed bytes (fullscreen vs restored): 0
- before sha256 (fullscreen): -
- after sha256 (restored): -
- fullscreen ppm: build/qemu_shared_renderer_fullscreen_2026_07_06/fullscreen.ppm (0 bytes)
- restored ppm: build/qemu_shared_renderer_fullscreen_2026_07_06/restored.ppm (0 bytes)
- serial log: build/qemu_shared_renderer_fullscreen_2026_07_06/serial.log (930 bytes)

This wrapper boots the wm-simple-web SimpleOS QEMU target directly
(same q35/qemu64/2G/BGA-std flags as os.qemu_runner._wm_simple_web_qmp_capture_target),
waits for the boot-time WM fullscreen demo to maximize window 0 to the
full framebuffer, captures the maximized framebuffer over the QMP
`pmemsave` channel, waits for the restore marker, captures the
restored framebuffer, and requires the two captures to differ by a
real pixel delta. It does not use blur, downscaling, tolerance
matching, or copied reference pixels.
