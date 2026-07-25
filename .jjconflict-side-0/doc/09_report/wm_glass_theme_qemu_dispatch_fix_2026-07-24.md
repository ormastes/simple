# SimpleOS WM Fullscreen Evidence

- status: fail
- reason: guest-render-fault
- wrapper: scripts/check/check-simpleos-wm-fullscreen-evidence.shs (sha256=640911e65cd94b32eba4075196a9bb4094c9571e9775b0c82f6d13f35de87b0b)
- simple bin: build/bootstrap-wm-classifier/stage3/aarch64-apple-darwin/simple
- resolved binary: /Users/ormastes/simple/build/bootstrap-wm-classifier/stage3/aarch64-apple-darwin/simple
- simple bin source: fresh-pure-simple-stage3-13d46d55
- simple bin status: pass
- simple bin version: simple-bootstrap 1.0.0-beta
- simple bin sha256: 13d46d55a80590b23c50d84695e3205427fb28f8814ef6a6a23e20e2b07c41e2
- qmp socket: build/wm_glass_theme_qemu_dispatch_fix_2026-07-24/qmp.sock
- kernel: build/wm_glass_theme_qemu_dispatch_fix_2026-07-24/simpleos_wm_production_desktop.elf (sha256=1ae59610e5e4c46c195a9ba7a16655c0d30d81e8bca8bd8102fc46453687f7a1)
- disk image: build/wm_glass_theme_qemu_dispatch_fix_2026-07-24/fat32-x86_64-font.img (pass, sha256=6dbb5c6a1228cb79be04ea02fa604ddb031bdffa1f3f1a83fc63e19eb2ebe604)
- pinned font asset: assets/fonts/google-fonts/ofl/notosansmono/NotoSansMono[wdth,wght].ttf (1708408 bytes, sha256=2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081)
- guest font marker: -
- font region: build/wm_glass_theme_qemu_dispatch_fix_2026-07-24/font-region.rgb (0 bytes, sha256=-, origin=qemu-pmemsave)
- scanout: address=2147483648 width=3840 height=2160 byte-pitch=15360 format=argb8888 generation=1
- host nonce: simpleos-wm-1784860433-18990
- input sequences: baseline=0 maximize=0 restore=0
- maximize IRQ/state/frame: - | - | -
- restore IRQ/state/frame: - | - | -
- changed bytes (baseline vs maximized): 0
- baseline sha256: -
- maximized sha256: -
- restored sha256: -
- baseline ppm: build/wm_glass_theme_qemu_dispatch_fix_2026-07-24/baseline.ppm (0 bytes)
- maximized ppm: build/wm_glass_theme_qemu_dispatch_fix_2026-07-24/fullscreen.ppm (0 bytes)
- restored ppm: build/wm_glass_theme_qemu_dispatch_fix_2026-07-24/restored.ppm (0 bytes)
- serial log: build/wm_glass_theme_qemu_dispatch_fix_2026-07-24/serial.log (153331 bytes)

This wrapper boots the wm-simple-web SimpleOS QEMU target directly
(same q35/max/2G/BGA-std flags as os.qemu_runner._wm_simple_web_qmp_capture_target),
derives QMP `pmemsave` address and size from the guest's validated
scanout marker, converts visible pixels using its byte pitch, injects
F11 through QEMU input, maps its host nonce to newly observed guest
input sequences, and requires sequence-correlated IRQ, WM state, and
frame-generation markers. Boot-time choreography is never
accepted as interaction evidence; missing correlation fails closed.
