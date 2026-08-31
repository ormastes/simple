# SimpleOS WM Fullscreen Evidence

- status: fail
- reason: guest-render-fault
- wrapper: scripts/check/check-simpleos-wm-fullscreen-evidence.shs (sha256=93128c926d555a3059400d3e35ec2045e6eaf2dc47b9112d3cebeab7c866dab3)
- simple bin: /Users/ormastes/simple/build/bootstrap/stage3/aarch64-apple-darwin/simple
- resolved binary: /Users/ormastes/simple/build/bootstrap/stage3/aarch64-apple-darwin/simple
- simple bin source: explicit-env
- simple bin status: pass
- simple bin version: simple-bootstrap 1.0.0-beta
- simple bin sha256: 0c766a4f0577488bddcb4efefc1f2450cc5cea5f5370ddbd950079e808827ea9
- qmp socket: build/simpleos_wm_fullscreen_evidence/qmp.sock
- kernel: build/simpleos_wm_fullscreen_evidence/simpleos_wm_production_desktop.elf (sha256=530c061fe1585b7958123b278363d87fcb42aa7fb04826975151e46c20271435)
- kernel build: current-source-built (wall timeout=900s)
- disk image: build/simpleos_wm_fullscreen_evidence/fat32-x86_64-font.img (pass, provenance=built-from-admitted-kernel, sha256=2a8f60e6431c3384a9013f22697ce5879afcfcb0f6bde09b0f960a30007ec168)
- browser demo: build/os/apps/browser_demo/browser_demo.elf (build=pass, disk=pass, sha256=8157eda3c0f2e610a5e75c4104a67246a018806adfa64cc436988e07d287943d)
- pinned font asset: host=assets/fonts/google-fonts/ofl/notosansmono/NotoSansMono[wdth,wght].ttf guest=/SYS/FONTS/NOTOSANS (1708408 bytes, sha256=2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081)
- guest font marker: -
- font region: build/simpleos_wm_fullscreen_evidence/font-region.rgb (0 bytes, sha256=-, origin=qemu-pmemsave)
- corrupt-copy calibration: build/simpleos_wm_fullscreen_evidence/font-region-corrupt-calibration.rgb (0 bytes, sha256=-, rejection=not-run)
- content provenance: -
- scanout: address=2147483648 width=3840 height=2160 byte-pitch=15360 format=argb8888 generation=1
- host nonce: simpleos-wm-1785891904-97359
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
- baseline ppm: build/simpleos_wm_fullscreen_evidence/baseline.ppm (0 bytes)
- maximized ppm: build/simpleos_wm_fullscreen_evidence/fullscreen.ppm (0 bytes)
- restored ppm: build/simpleos_wm_fullscreen_evidence/restored.ppm (0 bytes)
- browser event ppm: build/simpleos_wm_fullscreen_evidence/browser-event.ppm (0 bytes)
- serial log: build/simpleos_wm_fullscreen_evidence/serial.log (19041 bytes)

This wrapper boots the wm-simple-web SimpleOS QEMU target directly
(same q35/max/2G/BGA-std flags as os.qemu_runner._wm_simple_web_qmp_capture_target),
derives QMP `pmemsave` address and size from the guest's validated
scanout marker, converts visible pixels using its byte pitch, injects
F11 press/release plus a pointer click through QEMU input, maps each to newly
observed guest input sequences, requires both device receipts, and requires
sequence-correlated WM state and frame-generation only for key press. Boot-time choreography is never
accepted as interaction evidence; missing correlation fails closed.
