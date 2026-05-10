<!-- codex-impl -->
# SimpleOS RV64 Hosted QEMU Local Research

- Existing truthful hosted reference lives on x86_64 disk/UEFI lanes in [src/os/qemu_runner.spl](/home/ormastes/dev/pub/simple/src/os/qemu_runner.spl:1192) and [examples/simple_os/arch/x86_64/desktop_e2e_entry.spl](/home/ormastes/dev/pub/simple/examples/simple_os/arch/x86_64/desktop_e2e_entry.spl:1).
- Existing RV64 lane in [examples/simple_os/arch/riscv64/smoke_entry.spl](/home/ormastes/dev/pub/simple/examples/simple_os/arch/riscv64/smoke_entry.spl:1) is still a stub-backed smoke path. It reads seeded media markers and emits success without kernel/VFS/process/network proof.
- RV64 boot services in [src/os/kernel/boot/riscv_services.spl](/home/ormastes/dev/pub/simple/src/os/kernel/boot/riscv_services.spl:1) still report `storage: deferred`, so normal boot does not yet prove mounted VirtIO block storage.
- RV64 syscall dispatch in [src/os/kernel/arch/riscv64/syscall.spl](/home/ormastes/dev/pub/simple/src/os/kernel/arch/riscv64/syscall.spl:1) only handles a tiny hosted subset today.
- The immediate codebase need is truth, not false green: separate smoke from hosted, keep the guest alive for host probes, and stop the old RV64 smoke lane from printing process-backed desktop ownership markers.
