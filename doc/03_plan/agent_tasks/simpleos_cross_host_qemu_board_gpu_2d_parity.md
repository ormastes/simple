<!-- codex-plan -->
# SimpleOS Cross-Host QEMU and Native-Board GPU 2D Plan

## Scope and ownership

This plan extends, and does not replace:

- `doc/03_plan/agent_tasks/simpleos_qemu_host_gpu_2d.md`;
- `doc/03_plan/agent_tasks/simpleos_qemu_host_gpu_external_host_evidence.md`;
- `doc/03_plan/agent_tasks/macos_vulkan_metal_host_qemu_rendering_completion.md`;
- `doc/03_plan/agent_tasks/engine2d_qemu_exact_oracle.md`.

Those files retain QEMU protocol/live-evidence ownership. This lane owns the
shared target capability, exact artifact schema, board adapters, and physical
board evidence rows. Merge owner and generated-manual reviewer: primary
`/root`. Final reviewer: normal/highest-capability Codex or human independent
of the artifact producer.

## Shared names

- Interfaces: `TargetGpuCapabilityProvider`, `SimpleOsGuestGpuTransport`,
  `HostGpuAdapter`, `HostResourceInterop`, `NativeBoardGpuAdapter`.
- Evidence: `Engine2dParityArtifact`, `Engine2dParityReceipt`,
  `GpuCapabilityObservation`, `GpuEvidenceRung`.
- Setup/checkers: `setup_simpleos_native_board_gpu_fixture`,
  `check_device_origin_readback`, `check_engine2d_argb_metadata`,
  `check_exact_argb_parity`, `check_unavailable_gpu_row`.
- Placeholder: `fail("not implemented: <helper>")`.
- Manual steps are the exact phrases in
  `doc/03_plan/sys_test/simpleos_qemu_host_gpu_2d.md`.

## Work lanes

| Order | Lane | Deliverable | Depends on |
|---|---|---|---|
| 0 | compatibility freeze | unchanged Draw IR, RenderBackend, Metal/Vulkan, font, event, SIMD/software gates | current owned diffs reconciled |
| 1 | shared artifact | canonical ARGB metadata, SHA-256, mismatch diagnostics, capability cache/invalidation | lane 0 |
| 2 | Linux QEMU | existing ivshmem Vulkan row upgraded to full fixture; Venus/virgl/rutabaga kept separate | prepared Linux KVM/Vulkan host |
| 3 | macOS QEMU | shared Draw IR target and Metal-only source closure complete; produce supported daemon and ARM64 guests, then run native Metal host-offload; UTM Venus remains compatibility-only | admitted pure-Simple compiler and current ARM64 guest build |
| 4 | Windows QEMU | native DirectX host-offload row; upstream virtio acceleration remains blocked | prepared WHPX/DirectX host |
| 5 | board wrapper | one board identity/boot/driver/fence/readback schema and wrapper | lane 1 |
| 6 | UNO Q | Debian Adreno readiness, then SimpleOS-native driver row | physical UNO Q |
| 7 | UP Squared | Linux/Windows Intel readiness, then SimpleOS-native driver row | physical UP Squared N4200 |
| 8 | VisionFive 2 | vendor readiness; native row only after exact BXE support contract | physical board and supported driver |
| 9 | review/manual | requirement trace, generated manual, blocked-row audit, no-duplication review | all available rows |

## Environment postponement matrix

Postponement retains all acceptance criteria. It does not complete the umbrella
feature.

| Row | State | Missing prerequisite | Exact resume command | Retained artifacts | Owner |
|---|---|---|---|---|---|
| Linux QEMU Vulkan | postponed from this macOS session; active on prepared Linux | KVM, current pure-Simple compiler, Vulkan device/driver | `sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs` | `build/simpleos-host-gpu/`, `doc/09_report/` row | Linux GPU owner |
| Windows QEMU DirectX | postponed | Windows host, WHPX, hardware DirectX adapter, current compiler | `sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs` from the prepared Unix-compatible Windows environment or the documented PowerShell wrapper when added | `build/simpleos-host-gpu/`, encoded argv, serial/device receipt | Windows GPU owner |
| UNO Q native | postponed | physical ABX00162/ABX00173, SimpleOS boot/download path, Adreno firmware/driver owner | `sh scripts/check/check-simpleos-native-board-gpu-2d.shs --board uno-q --strict` (planned wrapper; implementation is FR-GPU-BOARD-0001) | `build/test-artifacts/simpleos-native-board-gpu-2d/uno-q/` | UNO Q board owner |
| VisionFive 2 native | blocked and postponed | physical board, exact BXE BVNC/firmware, supported driver, SimpleOS boot | `sh scripts/check/check-simpleos-native-board-gpu-2d.shs --board visionfive2 --strict` (planned wrapper; implementation is FR-GPU-BOARD-0002) | `build/test-artifacts/simpleos-native-board-gpu-2d/visionfive2/` | RISC-V board owner |
| UP Squared native | postponed | physical N4200 board, UEFI SimpleOS boot, Intel GPU firmware/memory/submission/display owners | `sh scripts/check/check-simpleos-native-board-gpu-2d.shs --board up-squared-n4200 --strict` (planned wrapper; implementation is FR-GPU-BOARD-0003) | `build/test-artifacts/simpleos-native-board-gpu-2d/up-squared-n4200/` | x86 board owner |

The existing external-host plan remains authoritative for detailed macOS,
Windows, CUDA, TODO 563, TODO 566, TODO 569, and TODO 570 resumption. Planned
board commands must fail closed until their wrapper exists; a missing wrapper
is not an unsupported hardware result.

The 2026-07-27 macOS implementation removed the monolithic entry-closure
blocker: Draw IR uses the shared internal target and `main_macos.spl` retains
only Metal providers. Resume the macOS row by admitting a supported pure-Simple
compiler, producing the daemon plus current ARM64 probe/desktop guests, and
then adding a verified ARM64-only wrapper selector and running the canonical
HVF command. macOS is not postponed and cached receipts cannot close it.

## Merge gates

1. No changes to public Simple 2D/Draw IR/backend/event/font interfaces; the
   internal executor target is dependency inversion only.
2. No duplicated renderer, atlas, cache, event router, or CPU oracle.
3. Exact device-origin artifact with `mismatch_count=0`.
4. Board Linux readiness cannot satisfy SimpleOS-native.
5. Every unavailable row remains `blocked`/`unsupported` in executable and
   generated-manual evidence.
6. Cooperative sidecar findings are accepted by the final reviewer.
7. Relevant architecture, design, guide, tracking, TODO, and SPipe state links
   are current before implementation verification.
