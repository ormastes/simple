# SimpleOS WM Fullscreen Evidence

- status: fail
- reason: guest-render-fault
- wrapper: scripts/check/check-simpleos-wm-fullscreen-evidence.shs (sha256=ee7aeb4522de191e1244a9c9ede5007ac09b15b65317d1bbbe8c1fe6f3cf5efc)
- simple bin: /Users/ormastes/simple/build/native_probe/simple
- resolved binary: /Users/ormastes/simple/build/native_probe/simple
- simple bin source: explicit-env
- simple bin status: pass
- simple bin version: simple-bootstrap 1.0.0-beta
- simple bin sha256: 93480fcc6f062dbe6a80a8f1276fddf235520c36b4d2ef8b8ca4c8c9a4f570c1
- qmp socket: /Users/ormastes/simple-clang-23-1-browser-demo/build/clang-23-1-qemu-evidence-sort-fix/qmp.sock
- kernel: /Users/ormastes/simple-clang-23-1-browser-demo/build/clang-23-1-qemu-evidence-sort-fix/simpleos_wm_production_desktop.elf (sha256=9bfe019ef761e70d02edc0c375d73080843cd8d4ab5ae2c76e2a937b2bdb34c2)
- kernel build: current-source-built (wall timeout=900s)
- disk image: /Users/ormastes/simple-clang-23-1-browser-demo/build/clang-23-1-qemu-evidence-sort-fix/fat32-x86_64-font.img (pass, provenance=built-from-admitted-kernel, sha256=b769a42b214871f58af8b05287235f21abaafabf76401d5c5b0545f5a7918f09)
- browser demo: build/os/apps/browser_demo/browser_demo.elf (build=pass, disk=pass, sha256=eaa4a5d444f1f2934983fcd6f2ba8b016b427b0ae90e381465f991ecea713abe)
- pinned font asset: host=assets/fonts/google-fonts/ofl/notosansmono/NotoSansMono[wdth,wght].ttf guest=/SYS/FONTS/NOTOSANS (1708408 bytes, sha256=2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081)
- guest font marker: -
- font region: /Users/ormastes/simple-clang-23-1-browser-demo/build/clang-23-1-qemu-evidence-sort-fix/font-region.rgb (0 bytes, sha256=-, origin=qemu-pmemsave)
- corrupt-copy calibration: /Users/ormastes/simple-clang-23-1-browser-demo/build/clang-23-1-qemu-evidence-sort-fix/font-region-corrupt-calibration.rgb (0 bytes, sha256=-, rejection=not-run)
- content provenance: -
- scanout: address=2147483648 width=3840 height=2160 byte-pitch=15360 format=argb8888 generation=1
- host nonce: simpleos-wm-1785816523-58064
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
- baseline ppm: /Users/ormastes/simple-clang-23-1-browser-demo/build/clang-23-1-qemu-evidence-sort-fix/baseline.ppm (0 bytes)
- maximized ppm: /Users/ormastes/simple-clang-23-1-browser-demo/build/clang-23-1-qemu-evidence-sort-fix/fullscreen.ppm (0 bytes)
- restored ppm: /Users/ormastes/simple-clang-23-1-browser-demo/build/clang-23-1-qemu-evidence-sort-fix/restored.ppm (0 bytes)
- browser event ppm: /Users/ormastes/simple-clang-23-1-browser-demo/build/clang-23-1-qemu-evidence-sort-fix/browser-event.ppm (0 bytes)
- serial log: /Users/ormastes/simple-clang-23-1-browser-demo/build/clang-23-1-qemu-evidence-sort-fix/serial.log (27809 bytes)

This wrapper boots the wm-simple-web SimpleOS QEMU target directly
(same q35/max/2G/BGA-std flags as os.qemu_runner._wm_simple_web_qmp_capture_target),
derives QMP `pmemsave` address and size from the guest's validated
scanout marker, converts visible pixels using its byte pitch, injects
F11 press/release plus a pointer click through QEMU input, maps each to newly
observed guest input sequences, requires both device receipts, and requires
sequence-correlated WM state and frame-generation only for key press. Boot-time choreography is never
accepted as interaction evidence; missing correlation fails closed.
