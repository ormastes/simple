# SimpleOS WM Fullscreen Evidence

- status: pass
- reason: pass
- wrapper: scripts/check/check-simpleos-wm-fullscreen-evidence.shs (sha256=728e7e02fa9659829ce07fd7888987bee98420a746810e47b18233685e5140c2)
- simple bin: build/bootstrap/stage3/aarch64-apple-darwin/simple
- resolved binary: /Users/ormastes/simple/build/bootstrap/stage3/aarch64-apple-darwin/simple
- simple bin source: explicit-env
- simple bin status: pass
- simple bin version: simple-bootstrap 1.0.0-beta
- simple bin sha256: 6faa17dbe4342c9fa94c48025c7c57cfdf150c1dea9b8cd9b99877610f9291e7
- qmp socket: build/simpleos_wm_fullscreen_evidence/qmp.sock
- kernel: build/simpleos_wm_fullscreen_evidence/simpleos_wm_production_desktop.elf (sha256=14d10a3d4d2485a132e291fb197fcc6ef3d692b732ac7c5aae94b77da2f6db8e)
- disk image: build/simpleos_wm_fullscreen_evidence/fat32-x86_64-font.img (pass, sha256=68589c49e533afd4badb7f645c81c9976dd9122ee94897343a73482043c0b93c)
- pinned font asset: assets/fonts/google-fonts/ofl/notosansmono/NotoSansMono[wdth,wght].ttf (1708408 bytes, sha256=2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081)
- guest font marker: [font-evidence] family=Noto Sans Mono asset_sha256=2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081 raster=pure-sfnt-glyf route=shared-wm-draw-ir component_id=taskbar-clock font_size=12 text=00:00 region=right56,bottom48 region_rgb_sha256=ffbd5f7690557565c42853ffd4fd4a6c6049203eaa0d8cc5f8cb981a409287c4
- font region: build/simpleos_wm_fullscreen_evidence/font-region.rgb (8064 bytes, sha256=ffbd5f7690557565c42853ffd4fd4a6c6049203eaa0d8cc5f8cb981a409287c4, origin=qemu-pmemsave)
- scanout: address=4160749568 width=3840 height=2160 byte-pitch=15360 format=argb8888 generation=1
- host nonce: simpleos-wm-1784326278-40373
- input sequences: baseline=0 maximize=1 restore=2
- maximize IRQ/state/frame: [wm-input-irq] input_seq=1 scancode=87 | [wm-state] input_seq=1 action=maximize window=1 maximized=true | [wm-frame] input_seq=1 generation=573379618
- restore IRQ/state/frame: [wm-input-irq] input_seq=2 scancode=87 | [wm-state] input_seq=2 action=restore window=1 maximized=false | [wm-frame] input_seq=2 generation=678551287
- changed bytes (baseline vs maximized): 19825470
- baseline sha256: 4c613cd6c0ac5129a84799fb15f6fb564fac9d78e7c8e0b04fd36c1f22ac0385
- maximized sha256: 7b128a9c19b2e39d9c58cf08a39311c72dd3eaa9f4d86274b94ac9ef3aae3dd4
- restored sha256: 4c613cd6c0ac5129a84799fb15f6fb564fac9d78e7c8e0b04fd36c1f22ac0385
- baseline ppm: build/simpleos_wm_fullscreen_evidence/baseline.ppm (24883217 bytes)
- maximized ppm: build/simpleos_wm_fullscreen_evidence/fullscreen.ppm (24883217 bytes)
- restored ppm: build/simpleos_wm_fullscreen_evidence/restored.ppm (24883217 bytes)
- serial log: build/simpleos_wm_fullscreen_evidence/serial.log (52344 bytes)

This wrapper boots the wm-simple-web SimpleOS QEMU target directly
(same q35/max/2G/BGA-std flags as os.qemu_runner._wm_simple_web_qmp_capture_target),
derives QMP `pmemsave` address and size from the guest's validated
scanout marker, converts visible pixels using its byte pitch, injects
F11 through QEMU input, maps its host nonce to newly observed guest
input sequences, and requires sequence-correlated IRQ, WM state, and
frame-generation markers. Boot-time choreography is never
accepted as interaction evidence; missing correlation fails closed.
