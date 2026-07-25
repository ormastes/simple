# SimpleOS WM Fullscreen Evidence

- status: fail
- reason: guest-render-fault
- wrapper: scripts/check/check-simpleos-wm-fullscreen-evidence.shs (sha256=da602f80010ed2b0af3d9c348206c51d8fb57bb1a7291109da61b6906ea966eb)
- simple bin: /Users/ormastes/simple/build/bootstrap/stage3/aarch64-apple-darwin/simple
- resolved binary: /Users/ormastes/simple/build/bootstrap/stage3/aarch64-apple-darwin/simple
- simple bin source: wm-glass-theme-postfix-stage3
- simple bin status: pass
- simple bin version: simple-bootstrap 1.0.0-beta
- simple bin sha256: 6351ee19835987b27cb3073bdaf253dee2f970671ec48910877368a51ede22d1
- qmp socket: /Users/ormastes/simple/build/wm_glass_theme_qemu_postfix3_2026-07-24/qmp.sock
- kernel: /Users/ormastes/simple/build/wm_glass_theme_qemu_postfix3_2026-07-24/simpleos_wm_production_desktop.elf (sha256=b87ce8820cf16cfe12c9fa35aacaa6f9e7c1dade741e4ef2b4ecfe868a8afbb4)
- disk image: /Users/ormastes/simple/build/wm_glass_theme_qemu_postfix3_2026-07-24/fat32-x86_64-font.img (pass, sha256=c2a286ee46631dfc64159f79d998666afe8aee838068f5ca4960252c675c87e7)
- pinned font asset: assets/fonts/google-fonts/ofl/notosansmono/NotoSansMono[wdth,wght].ttf (1708408 bytes, sha256=2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081)
- guest font marker: -
- font region: /Users/ormastes/simple/build/wm_glass_theme_qemu_postfix3_2026-07-24/font-region.rgb (0 bytes, sha256=-, origin=qemu-pmemsave)
- content provenance: -
- scanout: address=2147483648 width=3840 height=2160 byte-pitch=15360 format=argb8888 generation=1
- host nonce: simpleos-wm-1784868978-43380
- input sequences: baseline=0 maximize=0 restore=0
- maximize IRQ/state/frame: - | - | -
- restore IRQ/state/frame: - | - | -
- changed bytes (baseline vs maximized): 0
- baseline sha256: -
- maximized sha256: -
- restored sha256: -
- baseline ppm: /Users/ormastes/simple/build/wm_glass_theme_qemu_postfix3_2026-07-24/baseline.ppm (0 bytes)
- maximized ppm: /Users/ormastes/simple/build/wm_glass_theme_qemu_postfix3_2026-07-24/fullscreen.ppm (0 bytes)
- restored ppm: /Users/ormastes/simple/build/wm_glass_theme_qemu_postfix3_2026-07-24/restored.ppm (0 bytes)
- serial log: /Users/ormastes/simple/build/wm_glass_theme_qemu_postfix3_2026-07-24/serial.log (51672 bytes)

This wrapper boots the wm-simple-web SimpleOS QEMU target directly
(same q35/max/2G/BGA-std flags as os.qemu_runner._wm_simple_web_qmp_capture_target),
derives QMP `pmemsave` address and size from the guest's validated
scanout marker, converts visible pixels using its byte pitch, injects
F11 through QEMU input, maps its host nonce to newly observed guest
input sequences, and requires sequence-correlated IRQ, WM state, and
frame-generation markers. Boot-time choreography is never
accepted as interaction evidence; missing correlation fails closed.
