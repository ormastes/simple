# SimpleOS WM Fullscreen Evidence

- status: fail
- reason: dynamic-scanout-or-desktop-readiness-missing
- simple bin: build/bootstrap/stage3/aarch64-apple-darwin/simple
- simple bin source: explicit-env
- simple bin status: pass
- qmp socket: build/simpleos-wm-fullscreen-scalar-stage-serial-markers/qmp.sock
- scanout: address=4244635648 width=1024 height=768 byte-pitch=4096 format=argb8888 generation=1
- host nonce: simpleos-wm-1783765146-9586
- input sequences: baseline=0 maximize=0 restore=0
- maximize IRQ/state/frame: - | - | -
- restore IRQ/state/frame: - | - | -
- changed bytes (baseline vs maximized): 0
- baseline sha256: -
- maximized sha256: -
- restored sha256: -
- baseline ppm: build/simpleos-wm-fullscreen-scalar-stage-serial-markers/baseline.ppm (0 bytes)
- maximized ppm: build/simpleos-wm-fullscreen-scalar-stage-serial-markers/fullscreen.ppm (0 bytes)
- restored ppm: build/simpleos-wm-fullscreen-scalar-stage-serial-markers/restored.ppm (0 bytes)
- serial log: build/simpleos-wm-fullscreen-scalar-stage-serial-markers/serial.log (4729 bytes)

This wrapper boots the wm-simple-web SimpleOS QEMU target directly
(same q35/max/2G/BGA-std flags as os.qemu_runner._wm_simple_web_qmp_capture_target),
derives QMP `pmemsave` address and size from the guest's validated
scanout marker, converts visible pixels using its byte pitch, injects
F11 through QEMU input, maps its host nonce to newly observed guest
input sequences, and requires sequence-correlated IRQ, WM state, and
frame-generation markers. Boot-time choreography is never
accepted as interaction evidence; missing correlation fails closed.
