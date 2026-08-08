# Feature: SimpleOS CXL Device-Process Architecture

## Raw Request

"add next research doc and make improvexsimplecos plan for device driver in device, cxl friendly and etc.. check research doc and make pherallel agents plan SimpleOS CXL and device-process architecture"

The user supplied an extensive recommended architecture covering an L4-style microkernel/exokernel protection split, isolated driver processes, explicit host/coprocessor/device-resident placement, a unified device graph, capability-backed queues, CXL Type 3-first support, USB/HDA vertical slices, UNO Q constraints, QEMU evidence, observability, testing, and a contract-first parallel-agent plan.

## Task Type

feature

## Refined Goal

Produce repository-grounded local and domain research, selectable feature and NFR options, and an implementation-ready parallel-agent plan for a CXL-friendly SimpleOS device-process architecture that distinguishes host-isolated, coprocessor-remote, and genuinely device-resident execution.

## Acceptance Criteria

- AC-1: A Codex-tagged local research document identifies the current SimpleOS driver, process/IPC, PCI, DMA/IOMMU, xHCI, HDA, QEMU, CXL, and evidence-spine foundations with concrete repository paths and separates implemented behavior from proposals.
- AC-2: A Codex-tagged domain research document cites current primary sources for microkernel/exokernel driver isolation, IOMMU-safe user drivers, CXL device types and revisions, QEMU CXL limitations, USB HID/audio, and UNO Q hardware constraints.
- AC-3: The research states explicitly that CXL does not imply executable device-local driver capability and defines the prerequisites for `CoprocessorRemote` and `DeviceResident` placement.
- AC-4: Feature and NFR option documents provide two to four selectable alternatives per decision, each with description, pros, cons, and T-shirt/file-count effort; no option is auto-selected.
- AC-5: The agent-task plan fixes shared contract names, assigns exclusive file ownership, records dependencies, waves, acceptance gates, merge owner, final high-capability reviewer, sidecar lanes, and blocked physical-hardware rows with resume requirements.
- AC-6: The plan orders a real process/capability/DMA boundary before CXL policy and uses isolated xHCI-to-HID-to-compositor as the first device vertical slice.
- AC-7: CXL support is represented as capability levels/vector with CXL 2.0 Type 3/QEMU work first and CXL 4.0-compatible extensibility, while QEMU evidence is not promoted to real coherency, fabric, or hardware performance proof.
- AC-8: The plan includes security, generation/revocation, queue recovery, observability, QEMU evidence, UNO Q `NoCxl`, and real-hardware validation lanes without claiming unavailable rows as PASS.
- AC-9: Focused document checks confirm all new Markdown artifacts exist, contain no pending merge markers, and generated-spec layout remains valid; unrelated dirty work is preserved.
- AC-10: The lane stops after research/options/planning and asks the user to select feature and NFR options before final requirements, architecture, SSpec, implementation, or release work begins.

## Scope Exclusions

- No kernel, driver, runtime, QEMU runner, or test implementation in this research turn.
- No final requirements selection on the user's behalf.
- No claim of native UNO Q SimpleOS support, real CXL coherency, multi-host fabric support, or device-resident execution without physical evidence.
- No edits to unrelated dirty files owned by other active sessions.

## Cooperative Review

- Sidecar L1 — local repository audit: existing driver ABI, process/IPC, grants, PCI, xHCI, HDA, QEMU, and evidence paths.
- Sidecar L2 — domain/source audit: primary-source validation of CXL, QEMU, Fuchsia/seL4, IOMMUFD/VFIO, HID/audio, and UNO Q claims.
- Sidecar L3 — plan audit: dependency graph, ownership conflicts, acceptance gates, hardware-blocked rows, and risk ordering.
- Shared interfaces: `DriverManifestV2`, `DeviceNode`, `DriverPlacement`, `DriverLifecycle`, `DeviceQueue`, `QueueMemoryMode`, `ResourceLease`, `DeviceMemCapability`, `IrqCapability`, `DmaWindowCapability`, `SharedRegionCapability`, `NotificationCapability`, `ResetCapability`, `IoAddressSpace`, `IommuDomain`, and `CxlCapabilities`.
- Future manual-facing steps: `Establish an isolated synthetic driver boundary`; `Recover a driver with a new resource generation`; `Deliver USB input through isolated driver processes`; `Discover and configure a CXL Type 3 region`; `Relocate a poisoned CXL-backed device queue`.
- Future setup/checker helpers: `setup_simpleos_device_process_fixture`, `check_device_capability_revocation`, `check_q35_isolated_xhci_input`, `check_q35_cxl_type3_topology`, and `check_cxl_queue_relocation`.
- Any temporary future SSpec helper must fail explicitly with `assert(false)` or `fail(...)`; placeholder passes are forbidden.
- Merge owner and final normal/highest-capability reviewer: primary Codex agent (`/root`). Generated-manual review owner: primary Codex agent when the lane reaches SSpec; not part of this research-only turn.

## Selected Requirements

- Feature: Bundle A (`F1-A`, `F2-A`, `F3-A`, `F4-A`, `F5-A`)
- NFR: NFR-B mission-critical hardening

## Phase

research-done

## Log

- dev: Created state file with 10 acceptance criteria (type: feature); claimed only the `simpleos_cxl_device_process_architecture` documentation lane in a shared dirty checkout.
- research: Three read-only sidecars audited local implementation state, current primary sources, and plan dependencies/ownership. The primary agent merged and reviewed the findings.
- research: Added local/domain research, feature/NFR option documents, and an agent-task plan. Waiting for user selection; no final requirements or implementation work started.
- requirements: User selected Bundle A + NFR-B. Wrote final feature/NFR requirements, deleted option files, refreshed the SimpleOS guide, and advanced the lane to `research-done`.
