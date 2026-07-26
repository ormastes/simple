# SimpleOS Cross-Host QEMU and Native-Board GPU Requests

Shared requirement, research, architecture, design, test-plan, and execution
artifacts:

- `doc/02_requirements/feature/simpleos_qemu_host_gpu_2d.md`
- `doc/02_requirements/nfr/simpleos_qemu_host_gpu_2d.md`
- `doc/01_research/local/simpleos_qemu_host_gpu_2d.md`
- `doc/01_research/domain/simpleos_qemu_host_gpu_2d.md`
- `doc/04_architecture/simpleos_qemu_host_gpu_2d.md`
- `doc/05_design/simpleos_qemu_host_gpu_2d.md`
- `doc/03_plan/agent_tasks/simpleos_cross_host_qemu_board_gpu_2d_parity.md`
- `doc/03_plan/sys_test/simpleos_qemu_host_gpu_2d.md`

These requests deliberately share one Engine2D, transport-capability, parity
artifact, receipt, and CPU SIMD oracle contract.

## FR-GPU-QEMU-0001 — Complete cross-host QEMU GPU acceleration

- Filed-on: 2026-07-26
- Priority: P0
- Status: Open; Linux and Windows native execution postponed to prepared hosts
- Requested semantics: retain the current ivshmem host-service architecture for
  Linux Vulkan, macOS Metal, and Windows DirectX while keeping upstream
  virgl/Venus/rutabaga capability rows honest and separate.
- Acceptance criteria:
  - Linux, macOS, and Windows use one `SimpleOsGuestGpuTransport`.
  - Every native pass has correlated submission/fence/device-origin readback.
  - Exact Simple 2D bytes match the CPU SIMD oracle with zero mismatches.
  - Default VirtIO-GPU 2D remains presentation-only.

## FR-GPU-BOARD-0001 — Add UNO Q Adreno 702 native GPU adapter

- Filed-on: 2026-07-26
- Priority: P1
- Status: Open; postponed until a physical UNO Q and SimpleOS QRB2210 boot lane
  are available
- Requested semantics: reuse the shared Engine2D contract through an
  `UnoQAdrenoNativeBoardGpuAdapter`; do not treat the STM32U585 MCU lane or
  Debian Turnip/freedreno evidence as SimpleOS-native.
- Acceptance criteria:
  - Board identity and QRB2210 boot/download path are retained.
  - SimpleOS owns Adreno firmware, address space/cache, submission, fence,
    readback, and display integration.
  - Device-origin pixels exactly match the shared CPU SIMD oracle.

## FR-GPU-BOARD-0002 — Add VisionFive 2 BXE native GPU adapter

- Filed-on: 2026-07-26
- Priority: P1
- Status: Blocked request; current upstream Mesa lists BXE-4-32 unsupported
- Requested semantics: keep vendor Linux readiness separate and implement
  `VisionFive2PvrNativeBoardGpuAdapter` only after the exact BVNC, firmware,
  kernel, and userspace support contract is proven.
- Acceptance criteria:
  - The row stays blocked while upstream/vendor support is unavailable.
  - Vendor API-version output is never promoted to SimpleOS proof.
  - A future native pass includes SimpleOS boot, submission/fence, device
    identity/readback, and exact CPU SIMD parity.

## FR-GPU-BOARD-0003 — Add UP Squared N4200 Intel native GPU adapter

- Filed-on: 2026-07-26
- Priority: P1
- Status: Open; postponed until a physical N4200 board and native driver lane
  are available
- Requested semantics: reuse the shared Engine2D contract through an
  `UpSquaredIntelNativeBoardGpuAdapter`; Linux/Windows i915/ANV readiness
  informs the port but does not enter the Simple 2D public surface.
- Acceptance criteria:
  - UEFI SimpleOS board identity and boot transcript are retained.
  - SimpleOS owns Intel memory, queue, fence, readback, and display integration.
  - The exact device-origin artifact matches the shared CPU SIMD oracle.

## Resumption

Prerequisites, planned exact commands, retained artifact paths, owners, and
final reviewer are maintained in
`doc/03_plan/agent_tasks/simpleos_cross_host_qemu_board_gpu_2d_parity.md`.
