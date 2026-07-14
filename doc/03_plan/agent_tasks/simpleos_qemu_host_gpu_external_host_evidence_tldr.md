<!-- codex-plan -->
# SimpleOS QEMU Host-GPU External Hosts — TLDR

Status: **postponed**, not complete.

- GPU TODO119 (`mac_gpu_backend_evidence_2026-07-10.md`) owns macOS deployment.
- TODO544 owns Windows DirectX, macOS Metal, and prepared NVIDIA CUDA
  executor/QEMU receipts.
- TODO564 owns CUDA UUID/multi-GPU/MIG evidence.
- TODO563/569/570 postpone only non-current prepared-host rows; current Linux Vulkan rows stay active.
- Resume only with a prepared host and a compiler accepted by
  `simple_binary_is_valid`.
- Native PASS requires submission, completion, device readback, stable identity,
  exact parity, and correlated IDs.
- Translation, screenshots, flags, cached data, and CPU mirrors do not pass.
- Local TODO529/535/536/537/540/542/547/548/549/550/551/552/554/555/563/565/566/567/568/569/570 remains active.

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
