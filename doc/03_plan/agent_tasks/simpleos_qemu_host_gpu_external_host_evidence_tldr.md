<!-- codex-plan -->
# SimpleOS QEMU Host-GPU External Hosts — TLDR

Status: **external rows postponed; current-host work active; not complete**.

- GPU TODO119 (`mac_gpu_backend_evidence_2026-07-10.md`) owns macOS deployment.
- TODO544 owns Windows DirectX, macOS Metal, current-source CUDA, and CUDA QEMU receipts; retained-PTX CUDA readback passed locally.
- TODO564 retains two distinct local UUID-hash identities; MIG and CUDA QEMU evidence remain open.
- TODO563/569/570 postpone only non-current prepared-host rows; current Linux Vulkan rows stay active.
- TODO550's owner-level selector is implemented; the exact forced-Vulkan command is in the QEMU guide, but no live receipt is claimed.
- Resume only with a prepared host and a compiler accepted by
  `simple_binary_is_valid`.
- Native PASS requires submission, completion, device readback, stable identity,
  exact parity, and correlated IDs.
- Translation, screenshots, flags, cached data, and CPU mirrors do not pass.
- Local TODO529/535/536/537/540/542/547/548/549/550/551/552/554/555/563/565/566/567/568/569/570 remains active.
- Local retained-PTX CUDA evidence now has fail-closed exits, all-device stability/distinction, and artifact hashes; source regeneration, the Vulkan-only selector, MIG, and QEMU remain open.

```sdn
external_host_evidence {
  windows -> TODO544 -> directx_receipt
  macos -> TODO544 -> metal_receipt
  nvidia_linux -> TODO544 -> cuda_executor_receipt
  nvidia_linux -> TODO564 -> cuda_uuid_receipt
  native_rows -> [TODO569, TODO570, TODO563]
  all -> final_high_review
}
```
