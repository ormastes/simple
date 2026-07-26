# SimpleOS QEMU host-GPU postponed work

Host-only work completed on 2026-07-15:

- A diagnostic pure-Simple Stage 2/3 bootstrap succeeded; final source-matched admission remains postponed under TODO548.
- The explicit `host-gpu` runtime lane and Vulkan/CUDA provider checks passed at source/static level; no live GPU receipt is claimed.
- Host-side passthrough preflight classified unavailable guest-direct passthrough; live passthrough remains postponed.
- Linux host-daemon linking reached the Engine2D provider-closure boundary.

Postponed until the required lane or hardware is available:

- Engine2D provider split for Linux Vulkan/CUDA without DirectX/OpenCL/SIMD/font closure dependencies.
- Native x86 GPU readback and ProcessingIR timing receipts.
- AArch64 and RISC-V guest compile/boot/render receipts.
- Native Metal (macOS), DirectX (Windows), and CUDA-device receipts.
- Hardware-board validation and guest passthrough claims.

## Cross-host and native-board extension (2026-07-26)

Linux QEMU, Windows QEMU, UNO Q, VisionFive 2, and UP Squared native execution
are postponed from the current macOS research/design session. They remain
required rows, not exclusions or PASS.

The authoritative extension matrix, prerequisites, exact resume commands,
retained artifact paths, owners, and final reviewer are in:

`doc/03_plan/agent_tasks/simpleos_cross_host_qemu_board_gpu_2d_parity.md`.

Open feature requests are recorded in:

`doc/08_tracking/feature/simpleos_cross_host_board_gpu_requests_2026-07-26.md`.

VisionFive 2 is additionally blocked by current upstream Mesa documentation
listing BXE-4-32 as unsupported. UNO Q vendor/Debian acceleration and UP
Squared Linux/Windows driver readiness do not prove SimpleOS-native execution.
All rows require a current pure-Simple compiler, target boot identity,
submission/fence evidence, device-origin readback, and exact CPU SIMD parity
before promotion.

This ledger does not replace the conflicted shared TODO database; merge it there only after the other work lane resolves its conflicts.

## Current macOS execution blocker (2026-07-26)

The local Apple Silicon host has QEMU 10.2.2 and MoltenVK. Host API presence is
not guest acceleration evidence. The build-free host-GPU preflight selects HVF
for the same-ISA AArch64 row and TCG for the x86_64 and RISC-V rows, but all
three QEMU binaries are blocked because `ivshmem-plain` is absent. Accelerated
GL/rutabaga devices are also absent. Default VirtIO-GPU 2D remains available
for presentation only.

Resume this row only after a macOS QEMU deployment passes:

```sh
sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs --preflight
```

Then repair the independently failing Metal shader-provider initialization and
the pure-Simple CPU-SIMD evidence lane before running one fresh capped live
guest gate. Required promotion evidence remains: HVF in the executed AArch64
argv, guest negotiation, Metal device identity, device-origin readback, and
bit-exact parity with the CPU-SIMD oracle.
