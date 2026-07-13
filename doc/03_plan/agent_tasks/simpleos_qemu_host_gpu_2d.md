<!-- codex-design -->
# SimpleOS QEMU Host-GPU 2D Agent Tasks

## Shared Names Defined Before Sidecars

- Capsule: `SimpleOsHostGpuSession`
- Records: `SimpleOsHostGpuHello`, `SimpleOsHostGpuRequest`, `SimpleOsHostGpuReceipt`
- Wrapper: `scripts/check/check-simpleos-qemu-host-gpu-2d.shs`
- Manual steps: `Probe the QEMU guest GPU capability`; `Render and read back the Simple 2D parity fixture`; `Run the ProcessingIR parity fixture`; `Report device-backed host acceleration evidence`
- Setup/checkers: `simpleos_host_gpu_prepare_row`, `simpleos_host_gpu_validate_receipt`, `simpleos_host_gpu_compare_oracles`
- Placeholder: `fail("SimpleOS QEMU host-GPU protocol not implemented")`
- Checked dispatch: `vulkan_dispatch_framebuffer_compute_checked`; backend mapper: `_dispatch_framebuffer_checked`
- Checked IMAGE dispatch: `vulkan_dispatch_image_composite_checked`; manual step: `Render one clipped alpha IMAGE through Vulkan src-over`
- Checked-raw manual steps: `Dispatch the raw CLEAR and solid RECT fixture through checked Vulkan commands`; `Reject unchecked or fallback raw rendering before device-backed receipt`
- Checked-raw checkers: `submit_checked_clear_rect`; `expect_device_backed_clear_rect_readback`

## Lanes

| Lane | Owner | Deliverable |
|---|---|---|
| protocol codec/validation | Codex Spark | bounded Pure Simple records and malformed-input tests |
| x86_64 Linux Vulkan slice | Codex Spark | live guest/daemon render and processing receipt |
| AArch64/RISC-V adapters | Codex Spark | unchanged-protocol boot/probe rows |
| host backend review | lower-model sidecar | Metal/DirectX/CUDA/Vulkan capability classification |
| canonical WM command trace | Codex Spark | required RECT/TEXT/IMAGE/embedding subset and exclusions |
| checked Vulkan provenance trace | Codex Spark | shared tri-state dispatch owner and raw CLEAR/RECT test boundary |
| merge and generated-manual review | primary `/root` | wrapper/parser/manual accepted; native non-Linux rows remain open |
| final review | normal/highest-capability Codex | requirements, exclusions, security, NFR, manual quality |

Sidecars may not add raw `rt_*` aliases, architecture-specific public APIs,
fixture bypasses, synthetic handles, or passing placeholders.

## Current Handoff

- Wrapper and fail-closed self-test: implemented.
- Linux Vulkan live rows: x86_64, AArch64, and RV64 pass exact render and
  ProcessingIR receipts.
- Fresh pure-Simple guest builds: x86_64 and AArch64 pass; RV64 remains blocked
  at TODO 537's freestanding runtime/SBI owner boundary.
- Final reviewer: primary `/root`; Metal/DirectX/CUDA done marks remain rejected.
- Checked raw framebuffer dispatch: traced by Spark and accepted by the
  independent normal/highest-capability reviewer; production WM admission
  remains open for device-rendered offscreen opacity and p95 evidence. The
  reusable checked IMAGE src-over primitive is implemented.
