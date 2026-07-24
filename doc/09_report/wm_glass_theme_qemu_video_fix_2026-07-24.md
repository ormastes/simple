# SimpleOS WM Fullscreen Evidence

- status: fail
- reason: guest-render-fault
- wrapper: scripts/check/check-simpleos-wm-fullscreen-evidence.shs (sha256=640911e65cd94b32eba4075196a9bb4094c9571e9775b0c82f6d13f35de87b0b)
- simple bin: build/bootstrap/stage3/aarch64-apple-darwin/simple
- resolved binary: /Users/ormastes/simple/build/bootstrap/stage3/aarch64-apple-darwin/simple
- simple bin source: explicit-fresh-pure-simple-stage3
- simple bin status: pass
- simple bin version: simple-bootstrap 1.0.0-beta
- simple bin sha256: 6175ea1aa13576afe699a35a6521ed5defa258caefe0b4ca7da50a2cf813b62b
- qmp socket: build/wm_glass_theme_qemu_video_fix_2026-07-24/qmp.sock
- kernel: build/wm_glass_theme_qemu_fallback_2026-07-24/simpleos_wm_production_desktop.elf (sha256=c23c491776f1443aee04f1b92f7206190c083e93932df4987bcc9fcf84ad6e7e)
- disk image: build/wm_glass_theme_qemu_video_fix_2026-07-24/fat32-x86_64-font.img (pass, sha256=df7d33805842083e4ad204f762a21d024ff4155de8b9de7c70a5d96ceb1a43b7)
- pinned font asset: assets/fonts/google-fonts/ofl/notosansmono/NotoSansMono[wdth,wght].ttf (1708408 bytes, sha256=2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081)
- guest font marker: -
- font region: build/wm_glass_theme_qemu_video_fix_2026-07-24/font-region.rgb (0 bytes, sha256=-, origin=qemu-pmemsave)
- scanout: address=2147483648 width=3840 height=2160 byte-pitch=15360 format=argb8888 generation=1
- host nonce: simpleos-wm-1784855707-53873
- input sequences: baseline=0 maximize=0 restore=0
- maximize IRQ/state/frame: - | - | -
- restore IRQ/state/frame: - | - | -
- changed bytes (baseline vs maximized): 0
- baseline sha256: -
- maximized sha256: -
- restored sha256: -
- baseline ppm: build/wm_glass_theme_qemu_video_fix_2026-07-24/baseline.ppm (0 bytes)
- maximized ppm: build/wm_glass_theme_qemu_video_fix_2026-07-24/fullscreen.ppm (0 bytes)
- restored ppm: build/wm_glass_theme_qemu_video_fix_2026-07-24/restored.ppm (0 bytes)
- serial log: build/wm_glass_theme_qemu_video_fix_2026-07-24/serial.log (81284 bytes)

This wrapper boots the wm-simple-web SimpleOS QEMU target directly
(same q35/max/2G/BGA-std flags as os.qemu_runner._wm_simple_web_qmp_capture_target),
derives QMP `pmemsave` address and size from the guest's validated
scanout marker, converts visible pixels using its byte pitch, injects
F11 through QEMU input, maps its host nonce to newly observed guest
input sequences, and requires sequence-correlated IRQ, WM state, and
frame-generation markers. Boot-time choreography is never
accepted as interaction evidence; missing correlation fails closed.
