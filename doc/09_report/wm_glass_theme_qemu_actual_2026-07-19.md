# SimpleOS WM Fullscreen Evidence

- status: pass
- reason: pass
- wrapper: scripts/check/check-simpleos-wm-fullscreen-evidence.shs (sha256=72610f37255887cf5b0672e7ca8f84697adcde464e32b1ef4b0998b826b7f0e2)
- simple bin: /Users/ormastes/simple/build/bootstrap/stage3/aarch64-apple-darwin/simple
- resolved binary: /Users/ormastes/simple/build/bootstrap/stage3/aarch64-apple-darwin/simple
- simple bin source: auto-cached-pure-simple
- simple bin status: pass
- simple bin version: simple-bootstrap 1.0.0-beta
- simple bin sha256: 6faa17dbe4342c9fa94c48025c7c57cfdf150c1dea9b8cd9b99877610f9291e7
- qmp socket: build/wm_glass_theme_qemu_actual/qmp.sock
- kernel: build/wm_glass_theme_qemu_actual/simpleos_wm_production_desktop.elf (sha256=4bd9724b79d28b74c99512d3219ca94819e798aa64188ff17926bb223f4f8f9d)
- disk image: build/wm_glass_theme_qemu_actual/fat32-x86_64-font.img (pass, sha256=a80047b48e5de91c4610745bb0623084b209e8cc9c3b8760adca833bd3a2c316)
- pinned font asset: assets/fonts/google-fonts/ofl/notosansmono/NotoSansMono[wdth,wght].ttf (1708408 bytes, sha256=2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081)
- guest font marker: [font-evidence] family=Noto Sans Mono asset_sha256=2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081 raster=pure-sfnt-glyf route=shared-wm-draw-ir component_id=taskbar-clock font_size=12 text=00:00 region=right56,bottom48 region_rgb_sha256=addf76edf6d23ca9bea6d698ca1d30bc4bd8dd684bb50ff3158ef755bd2854fc
- font region: build/wm_glass_theme_qemu_actual/font-region.rgb (8064 bytes, sha256=addf76edf6d23ca9bea6d698ca1d30bc4bd8dd684bb50ff3158ef755bd2854fc, origin=qemu-pmemsave)
- scanout: address=2147483648 width=3840 height=2160 byte-pitch=15360 format=argb8888 generation=1
- host nonce: simpleos-wm-1784460700-18654
- input sequences: baseline=0 maximize=1 restore=2
- maximize IRQ/state/frame: [wm-input-irq] input_seq=1 scancode=87 | [wm-state] input_seq=1 action=maximize window=1 maximized=true | [wm-frame] input_seq=1 generation=573379618
- restore IRQ/state/frame: [wm-input-irq] input_seq=2 scancode=87 | [wm-state] input_seq=2 action=restore window=1 maximized=false | [wm-frame] input_seq=2 generation=678551287
- changed bytes (baseline vs maximized): 20043014
- baseline sha256: 340bd1205f6629b0b338ea5de23a78ab4a55a2704d53aee38be46b7aba942d2a
- maximized sha256: d2a601c15c807351194b7acecfffa2bc7940adfaf8563938b5dd59edc89141ce
- restored sha256: 340bd1205f6629b0b338ea5de23a78ab4a55a2704d53aee38be46b7aba942d2a
- baseline ppm: build/wm_glass_theme_qemu_actual/baseline.ppm (24883217 bytes)
- maximized ppm: build/wm_glass_theme_qemu_actual/fullscreen.ppm (24883217 bytes)
- restored ppm: build/wm_glass_theme_qemu_actual/restored.ppm (24883217 bytes)
- serial log: build/wm_glass_theme_qemu_actual/serial.log (52569 bytes)

This wrapper boots the wm-simple-web SimpleOS QEMU target directly
(same q35/max/2G/BGA-std flags as os.qemu_runner._wm_simple_web_qmp_capture_target),
derives QMP `pmemsave` address and size from the guest's validated
scanout marker, converts visible pixels using its byte pitch, injects
F11 through QEMU input, maps its host nonce to newly observed guest
input sequences, and requires sequence-correlated IRQ, WM state, and
frame-generation markers. Boot-time choreography is never
accepted as interaction evidence; missing correlation fails closed.
