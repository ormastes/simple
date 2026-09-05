# SimpleOS WM Fullscreen Evidence

- status: fail
- reason: guest-render-fault
- wrapper: scripts/check/check-simpleos-wm-fullscreen-evidence.shs (sha256=640911e65cd94b32eba4075196a9bb4094c9571e9775b0c82f6d13f35de87b0b)
- simple bin: /Users/ormastes/simple/build/bootstrap-wm-text-dispatch/stage4-cranelift/aarch64-apple-darwin/simple
- resolved binary: /Users/ormastes/simple/build/bootstrap-wm-text-dispatch/stage4-cranelift/aarch64-apple-darwin/simple
- simple bin source: wm-text-dispatch-stage4
- simple bin status: pass
- simple bin version: simple-bootstrap 1.0.0-beta
- simple bin sha256: 2d57ed3f76132dda43301c5bacc6bd2e5e5f6e114980de02e7eab30d17868763
- qmp socket: /Users/ormastes/simple/build/wm_glass_theme_qemu_postfix_2026-07-24/qmp.sock
- kernel: /Users/ormastes/simple/build/wm_glass_theme_qemu_postfix_2026-07-24/simpleos_wm_production_desktop.elf (sha256=e3c3b2251a0a8874a99a77355beb5f304ed4528c289a49f3a43f3b567b029df4)
- disk image: /Users/ormastes/simple/build/wm_glass_theme_qemu_postfix_2026-07-24/fat32-x86_64-font.img (pass, sha256=c18cd01dfbb30ce289a875afbf6dd14742608cc6e7c04ff8d5e89168ddd60e3e)
- pinned font asset: assets/fonts/google-fonts/ofl/notosansmono/NotoSansMono[wdth,wght].ttf (1708408 bytes, sha256=2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081)
- guest font marker: -
- font region: /Users/ormastes/simple/build/wm_glass_theme_qemu_postfix_2026-07-24/font-region.rgb (0 bytes, sha256=-, origin=qemu-pmemsave)
- scanout: address=2147483648 width=3840 height=2160 byte-pitch=15360 format=argb8888 generation=1
- host nonce: simpleos-wm-1784863923-41322
- input sequences: baseline=0 maximize=0 restore=0
- maximize IRQ/state/frame: - | - | -
- restore IRQ/state/frame: - | - | -
- changed bytes (baseline vs maximized): 0
- baseline sha256: -
- maximized sha256: -
- restored sha256: -
- baseline ppm: /Users/ormastes/simple/build/wm_glass_theme_qemu_postfix_2026-07-24/baseline.ppm (0 bytes)
- maximized ppm: /Users/ormastes/simple/build/wm_glass_theme_qemu_postfix_2026-07-24/fullscreen.ppm (0 bytes)
- restored ppm: /Users/ormastes/simple/build/wm_glass_theme_qemu_postfix_2026-07-24/restored.ppm (0 bytes)
- serial log: /Users/ormastes/simple/build/wm_glass_theme_qemu_postfix_2026-07-24/serial.log (119897 bytes)

This wrapper boots the wm-simple-web SimpleOS QEMU target directly
(same q35/max/2G/BGA-std flags as os.qemu_runner._wm_simple_web_qmp_capture_target),
derives QMP `pmemsave` address and size from the guest's validated
scanout marker, converts visible pixels using its byte pitch, injects
F11 through QEMU input, maps its host nonce to newly observed guest
input sequences, and requires sequence-correlated IRQ, WM state, and
frame-generation markers. Boot-time choreography is never
accepted as interaction evidence; missing correlation fails closed.
