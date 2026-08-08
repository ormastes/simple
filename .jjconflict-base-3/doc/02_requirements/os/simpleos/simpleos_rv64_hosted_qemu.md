<!-- codex-impl -->
# SimpleOS RV64 Hosted QEMU Requirements

- REQ-RV64-HOSTED-001: The repo must expose a first-class `riscv64-hosted` QEMU scenario distinct from the legacy `riscv64-virtio-fat32-smf` smoke lane.
- REQ-RV64-HOSTED-002: The `riscv64-hosted` lane must attach the RV64 filesystem image and user-mode networking with host forwards for guest SSH on host port `2222` and guest HTTP on host port `8080`.
- REQ-RV64-HOSTED-003: The RV64 shell script entrypoint must support a hosted mode that actively probes TCP reachability plus SSH and HTTP responses from the host side while the guest is running.
- REQ-RV64-HOSTED-004: Until RV64 guest SSH/HTTP services are real, the hosted lane must fail truthfully instead of reporting a green result from serial-only smoke markers.
- REQ-RV64-HOSTED-005: The existing `riscv64-virtio-fat32-smf` lane must be documented and described as a smoke-only SMF/VirtIO media probe, not as hosted or process-backed proof.
