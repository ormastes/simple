# Feature: SimpleOS QEMU Host-GPU 4K Capacity

## Raw Request
imple simpleos qemu host gpu 4k.....md

## Task Type
feature

## Refined Goal
Make the canonical SimpleOS QEMU desktop render a 3840x2160 frame through the shared host-GPU protocol when a supported backend is available, while retaining deterministic CPU fallback and auditable backend-failure evidence.

## Acceptance Criteria
- AC-1: The selected host-GPU capacity contract accepts a 3840x2160 ARGB frame, and a boundary test rejects the first unsupported frame size without overflow or truncation.
- AC-2: The canonical SimpleOS desktop entry negotiates a host-GPU backend at 3840x2160 and records a successful guest-observed frame submission/readback receipt when the current-host backend is available.
- AC-3: Metal, DirectX, and Vulkan rejection or timeout paths record guest-observed attempt intervals and select the next backend or CPU fallback without hanging, corrupting the frame, or bypassing the shared Draw IR to Engine2D path.
- AC-4: Host and SimpleOS window-manager producers continue to share `SharedWmScene`, `DrawIrComposition`, and the Engine2D lowering path; platform-specific code is limited to transport, device, framebuffer, and input adapters.
- AC-5: A QEMU 3840x2160 scenario proves desktop boot, one rendered WM frame, input delivery, and a non-empty screenshot or readback checksum; TCG is correctness-only and current-host native timing/RSS requirements follow the user-selected NFR.
- AC-6: Unit, integration, and SPipe system scenarios cover capacity negotiation, exact-4K success, over-capacity rejection, backend timeout/rejection, and CPU fallback with no placeholder assertions.
- AC-7: Generated `doc/06_spec` scenario documentation reads as an operator manual, and matching requirements, architecture, design, test plan, guide, feature tracking, and SPipe process artifacts are current before final verification.
- AC-8: Final verification passes the focused Simple checks, QEMU evidence gate, direct runtime/env guards, generated-spec layout guard, and requirement-to-test traceability without using the Rust seed as production evidence.

## Scope Exclusions
No Engine3D shortcut, no legacy direct-WM entry as production evidence, no unrelated GUI/web renderer repair, and no release or push.

## Cooperative Review
N/A: this is a bounded capacity-and-evidence correction on one existing shared protocol; parallel implementation would collide in the protocol contract and QEMU evidence wrapper, so the primary agent owns implementation and final review.

## Phase
dev-done

## Log
- dev: Created state file with 8 acceptance criteria (type: feature)

## Research Summary

### Existing Code

| Reference | Finding |
|---|---|
| `src/lib/common/gpu/simpleos_host_gpu_protocol.spl:5-21` | Protocol v1 fixes the shared region at 8 MiB; usable readback is below one 4K ARGB frame. |
| `src/os/compositor/engine2d_wm_frame_executor.spl:100-185` | Production WM rejects over-capacity frames before backend negotiation, then records per-attempt guest timing and fallback. |
| `src/os/kernel/ipc/host_gpu_ivshmem_map.spl:4-55` | Three ISA adapters assume 16 MiB placement strides; AArch64 also requires an exact 8 MiB BAR. |
| `src/os/kernel/arch/x86_64/host_gpu_ivshmem_vmm.spl:1-15` | x86_64 maps the shared BAR using the protocol-owned region bound. |
| `src/app/simpleos_gpu_host/daemon_runner.spl:168,493-511` | The daemon advertises, validates, maps, and unmaps exactly the protocol-owned region size. |
| `examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl:278-289,541` | Canonical x86 desktop requests 3840x2160 and enters the shared host-GPU WM executor. |
| `scripts/check/check-simpleos-qemu-host-gpu-2d.shs:299-318,540-590,785-786` | Evidence validates production receipts/negotiation but still creates an 8,388,608-byte ivshmem file. |
| `test/01_unit/lib/common/gpu/simpleos_host_gpu_protocol_spec.spl:5-77` | Existing unit coverage fixes version 1 assumptions and validates region/readback relationships. |

### Reusable Modules
- `simpleos_host_gpu_protocol` owns wire offsets, maxima, validation, status, and backend constants.
- `host_gpu_ivshmem` owns guest negotiation/submission/receipt transport; `simpleos_gpu_host` owns host mapping and execution.
- `SharedWmScene` -> `DrawIrComposition` -> `Engine2dWmFrameExecutor` is the canonical shared host/SimpleOS rendering path.

### Domain Notes
- A 32 MiB arena leaves enough bounded space for one exact 3840x2160 ARGB readback while preserving the current request/receipt model.
- Enlarging v1 is not mixed-binary compatible; a fixed-capacity change therefore needs coordinated protocol-version deployment.

### Open Questions
- User selection required: feature F1/F2/F3 and compatible NFR N1/N2/N3; escalated to intake.

<!-- sdn-diagram:id=simpleos_qemu_host_gpu_4k_capacity.research -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_qemu_host_gpu_4k_capacity.research hash=sha256:auto render=ascii
@layout dag
@direction LR

CanonicalDesktop -> SharedWmScene
SharedWmScene -> DrawIrComposition
DrawIrComposition -> Engine2dWmFrameExecutor
Engine2dWmFrameExecutor -> HostGpuProtocol
HostGpuProtocol -> GuestIvshmemBridge
GuestIvshmemBridge -> QemuIvshmemBAR
QemuIvshmemBAR -> HostGpuDaemon
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_qemu_host_gpu_4k_capacity.research hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

## Requirements

| Requirement | Source | Area |
|---|---|---|
| REQ-001: Accept exact 4K ARGB and reject the first over-capacity byte/dimension without overflow. | AC-1 | `src/lib/common/gpu/`, protocol unit specs |
| REQ-002: Canonical desktop negotiates and proves host-GPU submission/readback at 4K. | AC-2, AC-5 | compositor, desktop entry, QEMU evidence |
| REQ-003: Every rejected/timed-out backend has guest timing and deterministic selection/fallback evidence. | AC-3 | compositor, bridge, evidence wrapper |
| REQ-004: Host and SimpleOS retain the shared WM -> Draw IR -> Engine2D path. | AC-4 | `src/os/compositor/`, shared UI/Draw IR |
| REQ-005: Tests and manuals cover 4K, boundary, corrupt/stale, backend failure, and CPU fallback cases. | AC-6, AC-7 | `test/`, `doc/06_spec/`, plans/guides |
| REQ-006: Final focused checks and runtime/layout guards pass using the production self-hosted toolchain. | AC-8 | verification scripts and SPipe state |

## Phase
requirements-selection-required

## Log
- research: Found 3 reusable module groups, 8 existing code/test surfaces, and 6 requirements; selection remains escalated.
