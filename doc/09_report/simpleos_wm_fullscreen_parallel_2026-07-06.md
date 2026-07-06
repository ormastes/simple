# SimpleOS WM Fullscreen Evidence

- status: pass
- reason: pass
- simple bin: /Users/ormastes/simple/bin/release/aarch64-apple-darwin-macho/simple
- simple bin source: self-hosted:/Users/ormastes/simple/bin/release/aarch64-apple-darwin-macho/simple
- simple bin status: pass
- qmp socket: build/qemu_parallel_fullscreen_2026_07_06/qmp.sock
- fullscreen-enter marker: [wm-demo] fullscreen-enter window=0 size=1024x768
- fullscreen-exit marker: [wm-demo] fullscreen-exit window=0 restored=true
- fullscreen size: 1024x768 (width=1024 height=768)
- changed bytes (fullscreen vs restored): 2273500
- before sha256 (fullscreen): e3c2afd3c8c66fbe6f8248528f9b7ed8d1c9f4ff87494adf327588e4b215b4dc
- after sha256 (restored): fe59dff4f3bf54bb26946fc11802fffddfe388c4b37183e1810a8683e89f338c
- fullscreen ppm: build/qemu_parallel_fullscreen_2026_07_06/fullscreen.ppm (2359312 bytes)
- restored ppm: build/qemu_parallel_fullscreen_2026_07_06/restored.ppm (2359312 bytes)
- serial log: build/qemu_parallel_fullscreen_2026_07_06/serial.log (1387 bytes)

This wrapper boots the wm-simple-web SimpleOS QEMU target directly
(same q35/qemu64/2G/BGA-std flags as os.qemu_runner._wm_simple_web_qmp_capture_target),
waits for the boot-time WM fullscreen demo to maximize window 0 to the
full framebuffer, captures the maximized framebuffer over the QMP
`pmemsave` channel, waits for the restore marker, captures the
restored framebuffer, and requires the two captures to differ by a
real pixel delta. It does not use blur, downscaling, tolerance
matching, or copied reference pixels.
