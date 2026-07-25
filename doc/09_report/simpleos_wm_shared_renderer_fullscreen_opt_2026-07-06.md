# SimpleOS WM Fullscreen Evidence

- status: pass
- reason: pass
- simple bin: /Users/ormastes/simple/bin/release/aarch64-apple-darwin-macho/simple
- simple bin source: self-hosted:/Users/ormastes/simple/bin/release/aarch64-apple-darwin-macho/simple
- simple bin status: pass
- qmp socket: build/qemu_shared_renderer_fullscreen_opt_2026_07_06/qmp.sock
- fullscreen-enter marker: [wm-demo] fullscreen-enter window=0 size=1024x768
- fullscreen-exit marker: [wm-demo] fullscreen-exit window=0 restored=true
- fullscreen size: 1024x768 (width=1024 height=768)
- changed bytes (fullscreen vs restored): 2331510
- before sha256 (fullscreen): 402724de14eab7dc7ae95fd6940b6f8f26082348b7523b23bcb91439cd13201d
- after sha256 (restored): f6fe8418ef48288cbfbe44de7030d8f086091f0985629268bbf4368c6ca91979
- fullscreen ppm: build/qemu_shared_renderer_fullscreen_opt_2026_07_06/fullscreen.ppm (2359312 bytes)
- restored ppm: build/qemu_shared_renderer_fullscreen_opt_2026_07_06/restored.ppm (2359312 bytes)
- serial log: build/qemu_shared_renderer_fullscreen_opt_2026_07_06/serial.log (2187 bytes)

Additional shared-renderer serial evidence:

- `[web-demo] pixels-ready expected=128380`
- `[web-demo] renderer=shared_mdi_framebuffer_scene html=about:engine2d-wm checksum=25294231`
- `[backend-evidence] selected=qemu-framebuffer-cpu-simd renderer=shared_mdi_framebuffer_scene fallback=none frame_time_ms=unmeasured readback=unavailable:qemu-framebuffer-write-only`
- `[backend-evidence] present=direct-mmio-commit source=shared_mdi_framebuffer_scene`
- `[mdi-demo] html-renderable window=browser renderer=shared_mdi_framebuffer_scene pixels=128380 checksum=25294231`

This wrapper boots the wm-simple-web SimpleOS QEMU target directly
(same q35/qemu64/2G/BGA-std flags as os.qemu_runner._wm_simple_web_qmp_capture_target),
waits for the boot-time WM fullscreen demo to maximize window 0 to the
full framebuffer, captures the maximized framebuffer over the QMP
`pmemsave` channel, waits for the restore marker, captures the
restored framebuffer, and requires the two captures to differ by a
real pixel delta. It does not use blur, downscaling, tolerance
matching, or copied reference pixels.
