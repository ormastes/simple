# SimpleOS WM Fullscreen Evidence

- status: fail
- reason: guest-render-fault
- wrapper: scripts/check/check-simpleos-wm-fullscreen-evidence.shs (sha256=72610f37255887cf5b0672e7ca8f84697adcde464e32b1ef4b0998b826b7f0e2)
- simple bin: build/bootstrap-wm/stage3/aarch64-apple-darwin/simple
- resolved binary: /Users/ormastes/simple/build/bootstrap-wm/stage3/aarch64-apple-darwin/simple
- simple bin source: explicit-pure-simple-stage3
- simple bin status: pass
- simple bin version: simple-bootstrap 1.0.0-beta
- simple bin sha256: 80136adbdafae9ee8277c4dcb6717f1309bcd04de142a30bf0c3ffe9c11f331c
- qmp socket: build/wm_glass_theme_qemu_fresh_2026-07-24/qmp.sock
- kernel: build/wm_glass_theme_qemu_fresh_2026-07-24/simpleos_wm_production_desktop.elf (sha256=73b0983af74816b0c7e175dc642248b828e197d32935aabb4a4ddc466824d1c1)
- disk image: build/wm_glass_theme_qemu_fresh_2026-07-24/fat32-x86_64-font.img (pass, sha256=28f25a563fc84c77f017341ae0464dc55abfc1b93b58fbc87aa30b313e85ae0a)
- pinned font asset: assets/fonts/google-fonts/ofl/notosansmono/NotoSansMono[wdth,wght].ttf (1708408 bytes, sha256=2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081)
- guest font marker: -
- font region: build/wm_glass_theme_qemu_fresh_2026-07-24/font-region.rgb (0 bytes, sha256=-, origin=qemu-pmemsave)
- scanout: address=- width=0 height=0 byte-pitch=0 format=- generation=0
- host nonce: simpleos-wm-1784854340-84119
- input sequences: baseline=0 maximize=0 restore=0
- maximize IRQ/state/frame: - | - | -
- restore IRQ/state/frame: - | - | -
- changed bytes (baseline vs maximized): 0
- baseline sha256: -
- maximized sha256: -
- restored sha256: -
- baseline ppm: build/wm_glass_theme_qemu_fresh_2026-07-24/baseline.ppm (0 bytes)
- maximized ppm: build/wm_glass_theme_qemu_fresh_2026-07-24/fullscreen.ppm (0 bytes)
- restored ppm: build/wm_glass_theme_qemu_fresh_2026-07-24/restored.ppm (0 bytes)
- serial log: build/wm_glass_theme_qemu_fresh_2026-07-24/serial.log (4367 bytes)

This wrapper boots the wm-simple-web SimpleOS QEMU target directly
(same q35/max/2G/BGA-std flags as os.qemu_runner._wm_simple_web_qmp_capture_target),
derives QMP `pmemsave` address and size from the guest's validated
scanout marker, converts visible pixels using its byte pitch, injects
F11 through QEMU input, maps its host nonce to newly observed guest
input sequences, and requires sequence-correlated IRQ, WM state, and
frame-generation markers. Boot-time choreography is never
accepted as interaction evidence; missing correlation fails closed.
