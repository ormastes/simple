# SimpleOS WM Fullscreen Evidence

- status: fail
- reason: guest-render-fault
- wrapper: scripts/check/check-simpleos-wm-fullscreen-evidence.shs (sha256=cd6c883cee58cc6b06d6ea184718601fd52a09435ff00eb033f17679d389158c)
- simple bin: /home/ormastes/dev/pub/simple/build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple
- resolved binary: /home/ormastes/dev/pub/simple/build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple
- simple bin source: auto-cached-pure-simple
- simple bin status: pass
- simple bin version: simple-bootstrap 1.0.0-beta
- simple bin sha256: bed40ba33a43347a508eb9801c7bdfa9081e2ce98f81c55c076af577490710d9
- qmp socket: build/simpleos_wm_fullscreen_evidence/qmp.sock
- kernel: build/simpleos_wm_fullscreen_evidence/simpleos_wm_production_desktop.elf (sha256=2106fc8466883929f14e9f25e7f6091180d4ff1714e04ea583d330b844886ded)
- kernel build: current-source-built (wall timeout=900s)
- disk image: build/simpleos_wm_fullscreen_evidence/fat32-x86_64-font.img (pass, provenance=built-from-admitted-kernel, sha256=faa9e6047f3ca4a880404dad9085a0f7e44efdb8f0fba6392fbfffcfe9845be4)
- browser demo: build/os/apps/browser_demo/browser_demo.elf (build=pass, disk=pass, sha256=8968eb7a0293317749f5996e40d2971868fdacce962f805a495e32710a9cebdb)
- pinned font asset: host=assets/fonts/google-fonts/ofl/notosansmono/NotoSansMono[wdth,wght].ttf guest=/SYS/FONTS/NOTOSANS (1708408 bytes, sha256=2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081)
- guest font marker: -
- font region: build/simpleos_wm_fullscreen_evidence/font-region.rgb (0 bytes, sha256=-, origin=qemu-pmemsave)
- corrupt-copy calibration: build/simpleos_wm_fullscreen_evidence/font-region-corrupt-calibration.rgb (0 bytes, sha256=-, rejection=not-run)
- content provenance: -
- scanout: address=2147483648 width=3840 height=2160 byte-pitch=15360 format=argb8888 generation=1
- host nonce: simpleos-wm-1786370963-2340889
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
- serial log: build/simpleos_wm_fullscreen_evidence/serial.log (18344 bytes)

This wrapper boots the wm-simple-web SimpleOS QEMU target directly
(same q35/max/2G/BGA-std flags as os.qemu_runner._wm_simple_web_qmp_capture_target),
derives QMP `pmemsave` address and size from the guest's validated
scanout marker, converts visible pixels using its byte pitch, injects
F11 press/release plus a pointer click through QEMU input, maps each to newly
observed guest input sequences, requires both device receipts, and requires
sequence-correlated WM state and frame-generation only for key press. Boot-time choreography is never
accepted as interaction evidence; missing correlation fails closed.
