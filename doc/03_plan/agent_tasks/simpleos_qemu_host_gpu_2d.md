<!-- codex-design -->
# SimpleOS QEMU Host-GPU 2D Agent Tasks

## Shared Names Defined Before Sidecars

- Capsule: `SimpleOsHostGpuSession`
- Records: `SimpleOsHostGpuHello`, `SimpleOsHostGpuRequest`, `SimpleOsHostGpuReceipt`
- Wrapper: `scripts/check/check-simpleos-qemu-host-gpu-2d.shs`
- Manual steps: `Probe the QEMU guest GPU capability`; `Render and read back the Simple 2D parity fixture`; `Run the ProcessingIR parity fixture`; `Report device-backed host acceleration evidence`
- Setup/checkers: `simpleos_host_gpu_prepare_row`, `simpleos_host_gpu_validate_receipt`, `simpleos_host_gpu_compare_oracles`
- Placeholder: `fail("SimpleOS QEMU host-GPU protocol not implemented")`

## Lanes

| Lane | Owner | Deliverable |
|---|---|---|
| protocol codec/validation | Codex Spark | bounded Pure Simple records and malformed-input tests |
| x86_64 Linux Vulkan slice | Codex Spark | live guest/daemon render and processing receipt |
| AArch64/RISC-V adapters | Codex Spark | unchanged-protocol boot/probe rows |
| host backend review | lower-model sidecar | Metal/DirectX/CUDA/Vulkan capability classification |
| merge and generated-manual review | primary `/root` | integrated design, exact evidence, no false passes |
| final review | normal/highest-capability Codex | requirements, exclusions, security, NFR, manual quality |

Sidecars may not add raw `rt_*` aliases, architecture-specific public APIs,
fixture bypasses, synthetic handles, or passing placeholders.

