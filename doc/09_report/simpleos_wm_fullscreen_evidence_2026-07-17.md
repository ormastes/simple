# SimpleOS WM Fullscreen Evidence

- status: fail
- reason: capture-input-or-guest-correlation-failed
- wrapper: scripts/check/check-simpleos-wm-fullscreen-evidence.shs (sha256=cc7e335b67972730f5de2f4824a2f9cde73e64b606f80a0a9c23b6ff429cefae)
- simple bin: build/bootstrap/stage3/aarch64-apple-darwin/simple
- resolved binary: /Users/ormastes/simple/build/bootstrap/stage3/aarch64-apple-darwin/simple
- simple bin source: explicit-env
- simple bin status: pass
- simple bin version: simple-bootstrap 1.0.0-beta
- simple bin sha256: 6faa17dbe4342c9fa94c48025c7c57cfdf150c1dea9b8cd9b99877610f9291e7
- qmp socket: build/simpleos_wm_fullscreen_evidence/qmp.sock
- kernel: build/simpleos_wm_fullscreen_evidence/simpleos_wm_production_desktop.elf (sha256=cbb1491715569b5223bc00640ce1db04c426b9d9b04456325cd82d4c409e7555)
- disk image: build/simpleos_wm_fullscreen_evidence/fat32-x86_64-font.img (pass, sha256=3db3926310b555cdffd9ed5efc1db63b45a5b5b780f4e34487ba2b0cc432805d)
- pinned font asset: assets/fonts/google-fonts/ofl/notosansmono/NotoSansMono[wdth,wght].ttf (1708408 bytes, sha256=2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081)
- guest font marker: -
- font region: build/simpleos_wm_fullscreen_evidence/font-region.rgb (0 bytes, sha256=-, origin=qemu-pmemsave)
- scanout: address=4160749568 width=3840 height=2160 byte-pitch=15360 format=argb8888 generation=1
- host nonce: simpleos-wm-1784309779-53159
- input sequences: baseline=0 maximize=0 restore=0
- maximize IRQ/state/frame: - | - | -
- restore IRQ/state/frame: - | - | -
- changed bytes (baseline vs maximized): 0
- baseline sha256: -
- maximized sha256: -
- restored sha256: -
- baseline ppm: build/simpleos_wm_fullscreen_evidence/baseline.ppm (24883217 bytes)
- maximized ppm: build/simpleos_wm_fullscreen_evidence/fullscreen.ppm (0 bytes)
- restored ppm: build/simpleos_wm_fullscreen_evidence/restored.ppm (0 bytes)
- serial log: build/simpleos_wm_fullscreen_evidence/serial.log (50848 bytes)

This wrapper boots the wm-simple-web SimpleOS QEMU target directly
(same q35/max/2G/BGA-std flags as os.qemu_runner._wm_simple_web_qmp_capture_target),
derives QMP `pmemsave` address and size from the guest's validated
scanout marker, converts visible pixels using its byte pitch, injects
F11 through QEMU input, maps its host nonce to newly observed guest
input sequences, and requires sequence-correlated IRQ, WM state, and
frame-generation markers. Boot-time choreography is never
accepted as interaction evidence; missing correlation fails closed.
