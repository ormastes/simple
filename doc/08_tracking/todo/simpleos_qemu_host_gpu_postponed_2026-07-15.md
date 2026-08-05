# SimpleOS QEMU host-GPU postponed work

Host-only work completed on 2026-07-15:

- A diagnostic pure-Simple Stage 2/3 bootstrap succeeded; final source-matched admission remains postponed under TODO548.
- The explicit `host-gpu` runtime lane and Vulkan/CUDA provider checks passed at source/static level; no live GPU receipt is claimed.
- Host-side passthrough preflight classified unavailable guest-direct passthrough; live passthrough remains postponed.
- Linux host-daemon linking reached the Engine2D provider-closure boundary.

Postponed until the required lane or hardware is available:

- **TODO658**: UNO Q native GPU board row is physically unavailable in this lane. Add this as the explicit remaining blocker before finalizing the request:
  - Physical ABX00162/ABX00173 board attached.
  - Runner command for proof handoff:
    - `SIMPLE_BIN=<pure-simple-admitted> SIMPLEOS_UNOQ_BOARD_ATTACHED=1 sh scripts/check/check-simpleos-native-board-gpu-2d.shs --board uno-q --strict`
  - Required retained evidence: board identity and boot/download hashes, native adapter capability, submission/fence path, device identity, DrawIR event/audio/font receipts, device-origin readback, and CPU-SIMD parity.

- Engine2D provider split for Linux Vulkan/CUDA without DirectX/OpenCL/SIMD/font closure dependencies.
- Native x86 GPU readback and ProcessingIR timing receipts.
- AArch64 and RISC-V guest compile/boot/render receipts.
- Native Metal (macOS), DirectX (Windows), and CUDA-device receipts.
- Hardware-board validation and guest passthrough claims.

## Cross-host and native-board extension (2026-07-26)

Linux QEMU, Windows QEMU, UNO Q, VisionFive 2, and UP Squared native execution
are postponed from the current macOS research/design session. They remain
required rows, not exclusions or PASS.

The former extension-matrix path is not present in this checkout. The active,
fail-closed host handoffs are maintained in
`doc/08_tracking/feature/wm_glass_cross_host_evidence_requests_2026-07-27.md`
for the WM rows and in this ledger for the host-GPU rows. Postponement never
marks Windows, Linux, native Metal/Vulkan, x86_64, ARM64, or RV64 as PASS.

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

This is not a Homebrew configure-option omission that can be repaired by a
package upgrade: upstream QEMU documents traditional `ivshmem-plain` as a
Linux-host shared-memory device. The installed macOS binaries do expose
`virtio-serial`, and the preflight records that fact as
`virtio-serial-unimplemented`; it is not a host-GPU transport until SimpleOS
has a real framed VirtIO-console guest adapter, a host-daemon socket endpoint,
fence/completion semantics, and device-origin readback. It must never be
treated as Metal offload, guest-native Vulkan, or a scanout substitute.

The macOS AArch64 replacement is `file-backed-ram-tail`: QEMU realizes a
512 MiB `memory-backend-file` as the complete `virt` RAM region under HVF, and
SimpleOS reserves its final 8 MiB at GPA `0x5f800000` (file offset
`528482304`) for the existing bounded host-GPU wire protocol. The host daemon
maps only that exact 8 MiB offset. `pc-dimm` is not an alternative here: the
installed `virt` machine rejects it because `acpi-ged` is unavailable, even
with `acpi=on`. This remains host-Metal offload only; it neither accelerates
VirtIO-GPU scanout nor gives the guest native Vulkan.

Run the read-only classification command after any QEMU deployment change:

```sh
sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs --preflight
```

Only an upstream-compatible replacement transport with a completed SimpleOS
guest/host adapter may replace this blocked `ivshmem` row. Then repair the
independently failing Metal shader-provider initialization and the pure-Simple
CPU-SIMD evidence lane before running one fresh capped live guest gate.
Required promotion evidence remains: HVF in the executed AArch64 argv, guest
negotiation, Metal device identity, device-origin readback, and bit-exact
parity with the CPU-SIMD oracle.

## Active host-GPU resumption rows

All rows are active/fail-closed. Commands are resume commands only; they must
not be run with a bootstrap/seed executable or used to infer a pass.

| Row | Host/capability and missing prerequisite | Exact resume command | Retained artifacts | Owner | Final reviewer |
|---|---|---|---|---|---|
| macOS Metal host-GPU | macOS, HVF AArch64 QEMU, completed Metal-only daemon closure, admitted pure-Simple compiler/runtime; current blocker is the missing supported daemon closure and no admissible GUI runtime. | `sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs --preflight` (classification only); live gate resumes only after the missing transport/daemon and admission are independently approved. | executed argv/HVF receipt, guest negotiation, immutable Metal device/provider identity, device readback, CPU-SIMD parity, QMP/serial logs, timing/RSS. | prepared macOS host operator | independent highest-capability reviewer |
| Linux Vulkan host-GPU | physical Linux host, supported shared-memory transport, Vulkan daemon/provider closure, admitted compiler/runtime; no prepared host receipt. | `sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs --preflight` followed by the approved Linux host-gate command recorded with the admitted manifest. | manifest, daemon/QEMU logs, submission/fence, device readback, CPU-SIMD parity, timing/RSS. | prepared Linux host operator | independent highest-capability reviewer |
| Windows DirectX host-GPU | physical Windows host, supported transport and DirectX daemon/provider, admitted compiler/runtime; no prepared host receipt. | `sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs --preflight` followed by the approved Windows host-gate command recorded with the admitted manifest. | manifest, daemon/QEMU logs, submission/fence, device readback, CPU-SIMD parity, timing/RSS. | prepared Windows host operator | independent highest-capability reviewer |
| x86_64 QEMU | QEMU x86_64, firmware, current admitted kernel/disk and `grub-mkstandalone`; guest media is not admitted. | `BUILD_DIR=build/simpleos_wm_fullscreen_evidence SIMPLE_BIN=<admitted-simple> sh scripts/check/check-simpleos-wm-fullscreen-evidence.shs` | frozen manifest, kernel/disk hashes, serial/QMP/`pmemsave` captures, SSE2 parity, timing/RSS. | `/root/x86_qemu_owner` | independent highest-capability reviewer |
| ARM64 QEMU | QEMU AArch64, firmware, admitted ELF/FAT disk/manifest; live guest proof is missing. | `sh scripts/check/build-simpleos-arm64-desktop-engine2d-attested.shs` then `sh scripts/check/check-simpleos-arm64-qmp-input-evidence.shs` | frozen manifest, ELF/FAT hashes, serial/QMP/RAMFB captures, VirtIO/NEON receipts, timing/RSS. | `/root/arm_qemu_owner` | independent highest-capability reviewer |
| RV64 QEMU | QEMU RV64, current admitted ELF, modern PCI VirtIO input, QMP, and parity oracle; none has a current live receipt. | `bin/simple os build --scenario=riscv64-display-smoke` then `scripts/check/check-rv64-display-smoke-qmp-evidence.shs --wm-font-input` | frozen manifest, ELF hash, serial/QMP/RAMFB captures, PCI/ISR/input receipts, parity, timing/RSS. | prepared RV64 host operator | independent highest-capability reviewer |
