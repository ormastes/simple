# SimpleOS QEMU macOS GPU preflight — 2026-07-26

## Result

- Status: **BLOCKED**
- Host: macOS 26.5, Apple M4, AArch64
- QEMU: Homebrew 10.2.2
- Host Metal: available
- Host Vulkan: MoltenVK 1.4.1 exposes Apple M4
- SimpleOS guest Metal/Vulkan acceleration: **not proven**

Host Metal and MoltenVK availability do not prove a QEMU guest execution path.
Default VirtIO-GPU 2D is a scanout device in this deployment, not a
device-rendering receipt.

## Executed preflight

```sh
sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs --preflight
```

| Guest ISA | Selected accelerator | VirtIO-GPU 2D | ivshmem-plain | GL/rutabaga | Result |
|---|---|---:|---:|---:|---|
| x86_64 | TCG | yes | no | no | blocked |
| AArch64 | HVF | yes | no | no | blocked |
| RISC-V 64 | TCG | yes | no | no | blocked |

The selected architecture requires `ivshmem-plain` for the bounded shared-memory
guest-to-host Draw IR transport. None of the installed QEMU system binaries
advertises that device. They also expose no `virtio-gpu-gl`, `virtio-vga-gl`,
or rutabaga device. UTM is not installed.

## Fix completed in the wrapper

The host-GPU wrapper no longer hardcodes TCG. Same-ISA execution selects the
native accelerator advertised by QEMU: KVM on Linux, HVF on macOS, or WHPX on
Windows. Cross-ISA execution remains TCG correctness evidence. Native AArch64
uses `-cpu host`; AArch64 TCG keeps `-cpu cortex-a72`. Encoded argv validation
rejects mismatched accelerator/CPU pairs.

The new `--preflight` mode performs no SimpleOS build or guest boot and fails
closed when the selected transport is missing.

## Remaining blockers

1. Provide a macOS QEMU deployment whose executed preflight advertises
   `ivshmem_plain=yes`; do not infer this from package/configure metadata.
2. Fix the current Metal provider failure, reported as
   `Metal shader compilation failed`.
3. Produce nonzero native CPU-SIMD checksums and exact pixel evidence.
4. Run one fresh capped AArch64 HVF guest gate and retain negotiation, device
   identity, device-origin readback, framebuffer/input, and bit-exact parity.
5. Keep direct guest Vulkan/Venus experimental. It cannot replace the supported
   host-offload receipt.

## Verification performed

- wrapper shell syntax: PASS
- wrapper diff whitespace check: PASS
- focused native-accelerator argv contract: PASS
- real host `--preflight`: expected BLOCKED
- self-test: BLOCKED after the bounded candidate-frontend smoke was killed;
  no further retry was made because the lane reached its three-cycle limit
- live SimpleOS GPU boot: not run because preflight failed
