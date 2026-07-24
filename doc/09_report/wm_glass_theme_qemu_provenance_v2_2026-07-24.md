# SimpleOS WM Fullscreen Evidence

- status: fail
- reason: guest-render-fault
- wrapper: scripts/check/check-simpleos-wm-fullscreen-evidence.shs (sha256=8a2722d8f11c0ba5db57bf2ab971b3772bd40118d80de8dff00a2976d0e555a5)
- simple bin: /Users/ormastes/simple/build/bootstrap/stage2/aarch64-apple-darwin/simple
- resolved binary: /Users/ormastes/simple/build/bootstrap/stage2/aarch64-apple-darwin/simple
- simple bin source: wm-glass-theme-provenance-stage2
- simple bin status: pass
- simple bin version: simple-bootstrap 1.0.0-beta
- simple bin sha256: ec502b4621d35f512bb48f3e1cb8e93ecbdc507ccab33ad3990c29c5f7d0c9bf
- qmp socket: /Users/ormastes/simple/build/wm_glass_theme_qemu_provenance_v2_2026-07-24/qmp.sock
- kernel: /Users/ormastes/simple/build/wm_glass_theme_qemu_provenance_v2_2026-07-24/simpleos_wm_production_desktop.elf (sha256=845294e1d749bfccf44f1a24f691d95b7a53ecbe0cc5eda70e06f5156f49a96c)
- disk image: /Users/ormastes/simple/build/wm_glass_theme_qemu_provenance_v2_2026-07-24/fat32-x86_64-font.img (pass, sha256=f79ab7b3f0fc2754d0bb8220a498f9dc7b936a81fdba92c54f7c6fc9868aa7c0)
- pinned font asset: host=assets/fonts/google-fonts/ofl/notosansmono/NotoSansMono[wdth,wght].ttf guest=/SYS/FONTS/NOTOSANS (1708408 bytes, sha256=2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081)
- guest font marker: -
- font region: /Users/ormastes/simple/build/wm_glass_theme_qemu_provenance_v2_2026-07-24/font-region.rgb (0 bytes, sha256=-, origin=qemu-pmemsave)
- corrupt-copy calibration: /Users/ormastes/simple/build/wm_glass_theme_qemu_provenance_v2_2026-07-24/font-region-corrupt-calibration.rgb (0 bytes, sha256=-, rejection=not-run)
- content provenance: -
- scanout: address=2147483648 width=3840 height=2160 byte-pitch=15360 format=argb8888 generation=1
- host nonce: simpleos-wm-1784870006-43160
- input sequences: baseline=0 maximize=0 restore=0
- maximize IRQ/state/frame: - | - | -
- restore IRQ/state/frame: - | - | -
- pointer IRQ/state/frame: - | - | -
- pointer release IRQ/state/frame: - | - | -
- changed bytes (baseline vs maximized): 0
- baseline sha256: -
- maximized sha256: -
- restored sha256: -
- baseline ppm: /Users/ormastes/simple/build/wm_glass_theme_qemu_provenance_v2_2026-07-24/baseline.ppm (0 bytes)
- maximized ppm: /Users/ormastes/simple/build/wm_glass_theme_qemu_provenance_v2_2026-07-24/fullscreen.ppm (0 bytes)
- restored ppm: /Users/ormastes/simple/build/wm_glass_theme_qemu_provenance_v2_2026-07-24/restored.ppm (0 bytes)
- serial log: /Users/ormastes/simple/build/wm_glass_theme_qemu_provenance_v2_2026-07-24/serial.log (51611 bytes)

This wrapper boots the wm-simple-web SimpleOS QEMU target directly
(same q35/max/2G/BGA-std flags as os.qemu_runner._wm_simple_web_qmp_capture_target),
derives QMP `pmemsave` address and size from the guest's validated
scanout marker, converts visible pixels using its byte pitch, injects
F11 plus a pointer click through QEMU input, maps each to newly
observed guest input sequences, and requires sequence-correlated IRQ,
WM state, and frame-generation markers. Boot-time choreography is never
accepted as interaction evidence; missing correlation fails closed.
