<!-- codex-impl -->
# SimpleOS RV64 Hosted QEMU Architecture

This rollout separates two RV64 validation lanes.

- `riscv64-virtio-fat32-smf` remains the bounded smoke lane. It validates seeded VirtIO media and SMF probe helpers but does not count as hosted proof.
- `riscv64-hosted` is the truthful hosted-preflight lane. It boots a dedicated RV64 entry, enables VirtIO storage and networking, forwards host SSH/HTTP ports, keeps the guest alive, and leaves final acceptance to host-side probes.

The hosted-preflight entry in [examples/simple_os/arch/riscv64/hosted_entry.spl](/home/ormastes/dev/pub/simple/examples/simple_os/arch/riscv64/hosted_entry.spl:1) intentionally stops short of claiming userland-exec or SSH/HTTP success. It reports `HOSTED_PREFLIGHT_READY` only after POSIX init, network bring-up, and disk readability are in place.
