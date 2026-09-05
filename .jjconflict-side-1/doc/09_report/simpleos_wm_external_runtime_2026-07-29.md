# SimpleOS WM Fullscreen Evidence

- status: fail
- reason: dynamic-scanout-or-desktop-readiness-missing
- wrapper: scripts/check/check-simpleos-wm-fullscreen-evidence.shs (sha256=e81fb6cc22c70a4c8350dab0f1bdc55f5cad8ff54feea8694c4c8844ebe7b7e5)
- simple bin: /home/ormastes/dev/pub/simple/build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple
- resolved binary: /home/ormastes/dev/pub/simple/build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple
- simple bin source: existing-pure-simple-phase2
- simple bin status: pass
- simple bin version: simple-bootstrap 1.0.0-beta
- simple bin sha256: 58c2827c906fcdf2da5cdf47cab5d50a2da7430b59943dbbb9e31b91577892f4
- qmp socket: build/simpleos_wm_external_runtime/qmp.sock
- kernel: /home/ormastes/dev/pub/simple/build/os/simpleos_wm_x86_64.elf (sha256=f783a111a63ea781e447d6396cc33bf8be9f0723675479bec13a85ed9a33e4c9)
- kernel build: external-elf-validated (wall timeout=900s)
- disk image: build/simpleos_wm_external_runtime/fat32-x86_64-font.img (pass, provenance=built-from-external-elf-validated, sha256=fe65a6619d644463b55e3da1545d090379cc3395d986e2e864f21d756f006526)
- browser demo: build/os/apps/browser_demo/browser_demo.elf (build=pass, disk=pass, sha256=5f6088989e7305880c58699c7e73f51a3abf737ae342d83647a886bf414a5ee3)
- pinned font asset: host=assets/fonts/google-fonts/ofl/notosansmono/NotoSansMono[wdth,wght].ttf guest=/SYS/FONTS/NOTOSANS (1708408 bytes, sha256=2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081)
- guest font marker: -
- font region: build/simpleos_wm_external_runtime/font-region.rgb (0 bytes, sha256=-, origin=qemu-pmemsave)
- corrupt-copy calibration: build/simpleos_wm_external_runtime/font-region-corrupt-calibration.rgb (0 bytes, sha256=-, rejection=not-run)
- content provenance: -
- scanout: address=- width=0 height=0 byte-pitch=0 format=- generation=0
- host nonce: simpleos-wm-1785315842-853333
- input sequences: baseline=0 maximize-press=0 maximize-release=0 restore-press=0 restore-release=0
- maximize press IRQ/state/frame: - | - | -
- maximize release IRQ: -
- restore press IRQ/state/frame: - | - | -
- restore release IRQ: -
- pointer IRQ/state/frame: - | - | -
- pointer release IRQ/state/frame: - | - | -
- remote browser ready: -
- browser event/content apply: - | -
- browser content delta: changed=0 before=- after=-
- changed bytes (baseline vs maximized): 0
- baseline sha256: -
- maximized sha256: -
- restored sha256: -
- baseline ppm: build/simpleos_wm_external_runtime/baseline.ppm (0 bytes)
- maximized ppm: build/simpleos_wm_external_runtime/fullscreen.ppm (0 bytes)
- restored ppm: build/simpleos_wm_external_runtime/restored.ppm (0 bytes)
- browser event ppm: build/simpleos_wm_external_runtime/browser-event.ppm (0 bytes)
- serial log: build/simpleos_wm_external_runtime/serial.log (1253 bytes)

This wrapper boots the wm-simple-web SimpleOS QEMU target directly
(same q35/max/2G/BGA-std flags as os.qemu_runner._wm_simple_web_qmp_capture_target),
derives QMP `pmemsave` address and size from the guest's validated
scanout marker, converts visible pixels using its byte pitch, injects
F11 press/release plus a pointer click through QEMU input, maps each to newly
observed guest input sequences, requires both device receipts, and requires
sequence-correlated WM state and frame-generation only for key press. Boot-time choreography is never
accepted as interaction evidence; missing correlation fails closed.
