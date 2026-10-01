# WM Glass Theme Agent Tasks — TLDR

- 2026-07-25: hosted 16x16 pixels are diagnostic-only; x86 and ARM preflights
  pass without QEMU. Next: native `to_i64` fixture -> exact-current binary ->
  production host -> x86 QEMU -> ARM QEMU -> aggregate SSpec.

- Active integration worktree: `build/worktrees/wm-glass-theme`.
- Host and SimpleOS bootstrap ownership is now unified: host installs the
  resolved package snapshot; x86_64 and ARM64 install the generated Aetheric
  snapshot before compositor creation.
- Current-source production proof is still required for host, x86_64 QEMU, and
  ARM64 QEMU. The x86 route/SSE2 preflight passes without launching QEMU: the
  legacy render-event command now delegates to the canonical desktop capture.
  Host source and provider-link wiring are fixed, but the session's three host
  cycles are exhausted before launch; rebuild the compiler and recapture next
  session. The aggregate SSpec remains fail-fast.
- ARM64 now has source-preflight VirtIO-MMIO keyboard/pointer queues with
  DMA-order/status contracts and shared input translation. Live QMP key-edge,
  pointer-frame, WM-state, framebuffer-revision, and RAMFB captures remain
  unproven; UART is fallback-only.
- Read-only sidecars own history/CSS, host diagnosis, and QEMU diagnosis;
  `/root` owns merge, compiler preflight, evidence runs, final review, sync,
  and push.

```text
compiler preflight -> host capture -> x86 QEMU -> ARM QEMU/input
                   -> aggregate artifact reader -> final review
```
