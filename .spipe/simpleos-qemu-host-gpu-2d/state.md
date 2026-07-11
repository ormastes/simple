# Feature: SimpleOS QEMU Host-GPU 2D Hardening

## Raw Request
`$sp_dev harden simple 2d on qemue, specially x86,aarch,riscv. research simple os on qemu can use host gpu? metal,cuda,vulkan for process. rendering metal,directx,vulkan. make simple os qemu to use underlying gpu processing/rednering.`

## Task Type
feature

## Refined Goal
Make SimpleOS use a real QEMU-exposed host-accelerated GPU path for Simple 2D rendering and portable processing on x86_64, AArch64, and RISC-V where the host/QEMU stack supports it, with explicit capability detection, safe software fallback, and evidence that distinguishes device-backed execution from emulation or CPU rendering.

## Acceptance Criteria
- AC-1: Research documents identify the actual QEMU device, guest-driver, and host-renderer/compute paths available for Linux Vulkan/CUDA, macOS Metal, and Windows DirectX/Vulkan hosts, and explicitly classify unsupported combinations instead of claiming backend parity from API names alone.
- AC-2: Final selected requirements define pass/fail behavior for x86_64, AArch64, and RISC-V QEMU guests, including host prerequisites, capability negotiation, fallback behavior, rendering correctness, processing correctness, latency/RSS targets, and device-backed evidence.
- AC-3: Each target architecture boots the applicable SimpleOS QEMU image, probes the exposed GPU capability, and reports a stable backend/reason pair; an unavailable accelerated path selects the existing software/CPU fallback without boot failure or silent false-positive acceleration.
- AC-4: On every host/QEMU combination classified as supported, Simple 2D renders the canonical fixture through a guest-visible accelerated device, reads back the produced frame, and matches the CPU oracle using the repository's exact comparison contract.
- AC-5: Portable processing runs the same ProcessingIR fixture through the supported device-backed path and CPU oracle with matching results; CUDA, Vulkan, and CPU remain backend choices below ProcessingIR rather than separate public APIs.
- AC-6: Evidence proves real guest-to-QEMU-to-host GPU execution using negotiated virtio-gpu/virgl/venus/rutabaga or another researched supported device path plus host-side backend markers; screenshots, configured command-line flags, synthetic handles, and CPU mirrors alone fail the gate.
- AC-7: One canonical SPipe wrapper and scenario matrix cover x86_64, AArch64, and RISC-V, publish per-row `pass`, `unsupported`, `blocked`, or `fail` status with reasons, and feed `scripts/check/check-simpleos-hardening-evidence-matrix.shs` without weakening its existing 26/26 completion contract.
- AC-8: Focused tests cover capability negotiation, unsupported-device fallback, frame readback parity, processing parity, and fail-closed evidence parsing; executable specs live under `test/` and their generated operator-readable manuals live under `doc/06_spec/` as Markdown.
- AC-9: Final verification runs each acceptance check at most once after convergence, reports architecture/host limitations honestly, passes the direct runtime/env guards and generated-spec layout guard, and refreshes all changed architecture, plan, guide, report, SPipe-manual, skill/agent/command, and feature-tracking artifacts before any completion claim.

## Scope Exclusions
- Direct PCIe GPU passthrough/VFIO setup is excluded unless research shows it is required for a selected supported row; mediated/paravirtual QEMU GPU access is the default scope.
- A new public rendering or compute API is excluded; reuse Engine2D backend lanes and ProcessingIR.
- Unsupported host/guest combinations are not to be disguised with software rendering, API translation labels, or synthetic evidence.

## Cooperative Review
- Sidecar `qemu-gpu-domain`: QEMU/virtio-gpu/virgl/venus/rutabaga and Linux/macOS/Windows host-backend feasibility, including authoritative external sources.
- Sidecar `simpleos-gpu-local`: existing SimpleOS virtio-gpu, Engine2D, ProcessingIR, QEMU boot, and evidence-wrapper inventory; no edits.
- Sidecar `multiarch-evidence`: x86_64/AArch64/RISC-V boot and current hardening-matrix coverage/gaps; no edits.
- Merge owner: primary Codex `/root`.
- Final reviewer: primary normal/highest-capability Codex after sidecar evidence is merged; it owns requirement-option quality, exclusions, and generated-manual acceptance.
- Shared interfaces: existing `Engine2D` backend lane and `ProcessingIR`; capability/result records must use one shared guest-visible backend/reason contract rather than architecture-specific public APIs.
- Manual flow helpers: `step("Probe the QEMU guest GPU capability")`, `step("Render and read back the Simple 2D parity fixture")`, `step("Run the ProcessingIR parity fixture")`, and `step("Report device-backed host acceleration evidence")`.
- Setup/checker helpers: reuse `scripts/check/check-simpleos-hardening-evidence-matrix.shs`; the lane-owned focused wrapper name is `scripts/check/check-simpleos-qemu-host-gpu-2d.shs` only if no existing wrapper already covers all rows.
- Fail-fast placeholders: temporary scenario/helper bodies must use `fail("simpleos-qemu-host-gpu-2d not implemented")` and may not use passing stubs or synthetic acceleration markers.
- Generated-manual review owner: primary Codex `/root`.

## Phase
requirements-done

## Log
- dev: Created state file with 9 acceptance criteria (type: feature); implementation and verification are intentionally deferred to subsequent SPipe phases.
- research: Restored current local/domain research after the earlier shared-checkout artifacts disappeared; current source still proves CPU raster plus VirtIO-GPU 2D scanout only.
- requirements: User selected Feature B (cross-host QEMU GPU service) and NFR B (balanced desktop target); finalized `doc/02_requirements/feature/simpleos_qemu_host_gpu_2d.md` and `doc/02_requirements/nfr/simpleos_qemu_host_gpu_2d.md`.
