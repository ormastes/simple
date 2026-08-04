# SimpleOS WM Fullscreen Evidence

- status: fail
- reason: dynamic-scanout-or-desktop-readiness-missing
- wrapper: scripts/check/check-simpleos-wm-fullscreen-evidence.shs (sha256=86aa726090fffe6f62ac4686bd52f6f6416f7e689b9a6a9c39cd0630e8c9f434)
- simple bin: /Users/ormastes/simple/bin/release/aarch64-apple-darwin-macho/simple
- resolved binary: /Users/ormastes/simple/bin/release/aarch64-apple-darwin-macho/simple
- simple bin source: explicit-env
- simple bin status: pass
- simple bin version: Simple v1.0.0-beta
- simple bin sha256: f2c216a660da83da1a253d2e8191a3059a66b1d9dc11bbcbaf237fe7e5b8d2bc
- qmp socket: /Users/ormastes/simple-clang-23-1-browser-demo/build/clang-23-1-qemu-evidence-phase-artifact/qmp.sock
- kernel: /Users/ormastes/simple/build/simpleos_wm_fullscreen_evidence/simpleos_wm_production_desktop.elf (sha256=4d6443880c261bbdaf4d1762fc019a6e4b1f7912befb83849748477a5ce879c5)
- kernel build: external-elf-validated (wall timeout=900s)
- disk image: /Users/ormastes/simple-clang-23-1-browser-demo/build/clang-23-1-qemu-evidence-phase-artifact/fat32-x86_64-font.img (pass, provenance=built-from-external-elf-validated, sha256=49b97a0cdb396fe97ee79303dce431e35f5f5cdbafa021d41fcea8e6306b8869)
- browser demo: build/os/apps/browser_demo/browser_demo.elf (build=pass, disk=pass, sha256=eaa4a5d444f1f2934983fcd6f2ba8b016b427b0ae90e381465f991ecea713abe)
- pinned font asset: host=assets/fonts/google-fonts/ofl/notosansmono/NotoSansMono[wdth,wght].ttf guest=/SYS/FONTS/NOTOSANS (1708408 bytes, sha256=2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081)
- guest font marker: -
- font region: /Users/ormastes/simple-clang-23-1-browser-demo/build/clang-23-1-qemu-evidence-phase-artifact/font-region.rgb (0 bytes, sha256=-, origin=qemu-pmemsave)
- corrupt-copy calibration: /Users/ormastes/simple-clang-23-1-browser-demo/build/clang-23-1-qemu-evidence-phase-artifact/font-region-corrupt-calibration.rgb (0 bytes, sha256=-, rejection=not-run)
- content provenance: -
- scanout: address=- width=0 height=0 byte-pitch=0 format=- generation=0
- host nonce: simpleos-wm-1785814149-42705
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
- baseline ppm: /Users/ormastes/simple-clang-23-1-browser-demo/build/clang-23-1-qemu-evidence-phase-artifact/baseline.ppm (0 bytes)
- maximized ppm: /Users/ormastes/simple-clang-23-1-browser-demo/build/clang-23-1-qemu-evidence-phase-artifact/fullscreen.ppm (0 bytes)
- restored ppm: /Users/ormastes/simple-clang-23-1-browser-demo/build/clang-23-1-qemu-evidence-phase-artifact/restored.ppm (0 bytes)
- browser event ppm: /Users/ormastes/simple-clang-23-1-browser-demo/build/clang-23-1-qemu-evidence-phase-artifact/browser-event.ppm (0 bytes)
- serial log: /Users/ormastes/simple-clang-23-1-browser-demo/build/clang-23-1-qemu-evidence-phase-artifact/serial.log (5066 bytes)

This wrapper boots the wm-simple-web SimpleOS QEMU target directly
(same q35/max/2G/BGA-std flags as os.qemu_runner._wm_simple_web_qmp_capture_target),
derives QMP `pmemsave` address and size from the guest's validated
scanout marker, converts visible pixels using its byte pitch, injects
F11 press/release plus a pointer click through QEMU input, maps each to newly
observed guest input sequences, requires both device receipts, and requires
sequence-correlated WM state and frame-generation only for key press. Boot-time choreography is never
accepted as interaction evidence; missing correlation fails closed.
