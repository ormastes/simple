# Shared SOSIX/QEMU Settings — TLDR

```text
descriptor -> isolated media -> QEMU -> serial -> guest ls/program -> bundle
```

- Canonical descriptor: `src/os/qemu_systest_contract.spl`.
- Canonical executor: `src/os/_QemuRunner/`.
- Host preflight: settings plus `scripts/qemu/simple-qemu-host-admission.shs`; host relabeling is rejected.
- Matrix: Unix `scripts/check/check-sosix-qemu-matrix.shs --all-guests --preflight`; Windows `scripts/check/check-sosix-qemu-matrix.ps1 -AllGuests -Preflight`.
- Add `--run --parallel` or `-Run -Parallel` for isolated wait-all six-row execution.
- Import the 24 native-host receipts with `scripts/check/collect-sosix-qemu-evidence.shs`.
- Storage precedence: `SIMPLE_BIG_STORAGE_ROOT` → local setting → `~/.simple`; this host selects `/mnt/data/.simple`.
- Never copy argv or silently fall back.
- Cover Linux/Windows/macOS/FreeBSD and x86/ARM/RISC-V 32/64.
- Every guest proves boot, mounted-filesystem listing, and arbitrary program run.
- Compiler rows prove target-native Simple version and hello compile/run.
- TCG is correctness-only; native credit requires KVM/HVF/WHPX in executed argv.
- Missing prerequisites remain blocked with an exact resume command.
