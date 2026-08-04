# SimpleOS WM Fullscreen Evidence

- status: fail
- reason: guest-render-fault
- wrapper: scripts/check/check-simpleos-wm-fullscreen-evidence.shs (sha256=d89d3b3a04cd7dd74856776a7397ffaa4f743e0e059730d1bc64b0d2ba3d3ff9)
- simple bin: /Users/ormastes/simple/build/native_probe/simple
- resolved binary: /Users/ormastes/simple/build/native_probe/simple
- simple bin source: explicit-native-probe-provider-artifact
- simple bin status: pass
- simple bin version: simple-bootstrap 1.0.0-beta
- simple bin sha256: 93480fcc6f062dbe6a80a8f1276fddf235520c36b4d2ef8b8ca4c8c9a4f570c1
- qmp socket: build/clang-23-1-qemu-evidence-sort-fix/qmp.sock
- kernel: build/clang-23-1-qemu-evidence-sort-fix/simpleos_wm_production_desktop.elf (sha256=6a016269065000946c970de19f009891ed1b9129b6d995293033deac3ac7974b)
- kernel build: current-source-built (wall timeout=900s)
- disk image: build/clang-23-1-qemu-evidence-sort-fix/fat32-x86_64-font.img (pass, provenance=built-from-admitted-kernel, sha256=07f96795922e62d1a3b36394ee4dc9563d258619032a07bae764d1a8756f68ee)
- browser demo: build/os/apps/browser_demo/browser_demo.elf (build=pass, disk=pass, sha256=eaa4a5d444f1f2934983fcd6f2ba8b016b427b0ae90e381465f991ecea713abe)
- pinned font asset: host=assets/fonts/google-fonts/ofl/notosansmono/NotoSansMono[wdth,wght].ttf guest=/SYS/FONTS/NOTOSANS (1708408 bytes, sha256=2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081)
- guest font marker: -
- font region: build/clang-23-1-qemu-evidence-sort-fix/font-region.rgb (0 bytes, sha256=-, origin=qemu-pmemsave)
- corrupt-copy calibration: build/clang-23-1-qemu-evidence-sort-fix/font-region-corrupt-calibration.rgb (0 bytes, sha256=-, rejection=not-run)
- content provenance: -
- scanout: address=2147483648 width=3840 height=2160 byte-pitch=15360 format=argb8888 generation=1
- host nonce: simpleos-wm-1785826924-2767
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
- baseline ppm: build/clang-23-1-qemu-evidence-sort-fix/baseline.ppm (0 bytes)
- maximized ppm: build/clang-23-1-qemu-evidence-sort-fix/fullscreen.ppm (0 bytes)
- restored ppm: build/clang-23-1-qemu-evidence-sort-fix/restored.ppm (0 bytes)
- browser event ppm: build/clang-23-1-qemu-evidence-sort-fix/browser-event.ppm (0 bytes)
- serial log: build/clang-23-1-qemu-evidence-sort-fix/serial.log (26085 bytes)

This wrapper boots the wm-simple-web SimpleOS QEMU target directly
(same q35/max/2G/BGA-std flags as os.qemu_runner._wm_simple_web_qmp_capture_target),
derives QMP `pmemsave` address and size from the guest's validated
scanout marker, converts visible pixels using its byte pitch, injects
F11 press/release plus a pointer click through QEMU input, maps each to newly
observed guest input sequences, requires both device receipts, and requires
sequence-correlated WM state and frame-generation only for key press. Boot-time choreography is never
accepted as interaction evidence; missing correlation fails closed.
