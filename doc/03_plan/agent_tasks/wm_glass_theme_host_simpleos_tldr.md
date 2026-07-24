# WM Glass Theme Agent Tasks — TLDR

- Active integration worktree: `build/worktrees/wm-glass-theme`.
- Host and SimpleOS bootstrap ownership is now unified: host installs the
  resolved package snapshot; x86_64 and ARM64 install the generated Aetheric
  snapshot before compositor creation.
- Current-source production proof is still required for host, x86_64 QEMU, and
  ARM64 QEMU. The aggregate SSpec remains fail-fast until those artifacts and
  event receipts are real.
- Read-only sidecars own history/CSS, host diagnosis, and QEMU diagnosis;
  `/root` owns merge, compiler preflight, evidence runs, final review, sync,
  and push.

```text
compiler preflight -> host capture -> x86 QEMU -> ARM QEMU/input
                   -> aggregate artifact reader -> final review
```
