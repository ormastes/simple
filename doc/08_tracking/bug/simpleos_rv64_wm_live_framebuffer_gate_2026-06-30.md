# SimpleOS RV64 WM Live Framebuffer Gate Missing

- status: source-ready-contract-v2-live-proof-pending
- gate: `scripts/check/check-simpleos-host-configuration-matrix.shs`
- failing field: `simpleos_host_configuration_qemu_riscv64_wm_live_status=missing`
- current source: `examples/09_embedded/simple_os/arch/riscv64/gui_entry_desktop.spl`
- latest result: canonical source and contract-v2 parser are present; TODO 548 still blocks a fresh pure-Simple ELF/QEMU capture

The smaller `riscv64-display-smoke` scenario now routes the renamed production
entry through `src/os` and `src/lib`. Its architecture facade discovers the
VirtIO mode dynamically, `FramebufferDriver` exposes that scanout to the
canonical compositor, and `DesktopShell` renders through
`Engine2dWmFrameExecutor` before the sole checked transfer/flush present.
Optional host execution reuses the existing ivshmem mapper and RV64 protocol
identity; it does not create a private renderer.

Evidence contract v2 rejects the old fixed-resolution/anchor report. A passing
fresh report must correlate one positive scene revision across ordered render,
present, and ready markers, validate PPM dimensions/stride/completeness, and
observe at least four canonical desktop palette roles. TODO 567 remains open
for replacing the facade's transitional C DMA/queue transport with pure Simple.
TODO 548 remains the live-build blocker, so source and parser work do not close
this bug or claim QEMU/physical-board PASS.

Historical scanout-probe evidence:
- `riscv64-display-smoke` boots the display probe.
- QMP capture proves a nonblank framebuffer:
  `rv64_display_smoke_qmp_nonblack=76800`.
- Capture validates WM anchors comparable to the current MDI gate. PASS:
  `rv64_display_smoke_qmp_wm_anchor_matches=5`.
- `check-simpleos-host-configuration-matrix.shs` reports
  `qemu_riscv64_wm_live: pass`. PASS.
