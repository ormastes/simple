# Lane: GPU MMU (ex-codex 019fb820)
Goal: GPU MMU design/contract + residency. Docs exist: `doc/05_design/gpu_mmu.md`; commit 75e6b1e8435 design(gpu-mmu): freeze residency interfaces.
Last state: this lane file remains active as a handoff tracker. System-level coverage artifacts now exist (`test/03_system/lib/gpu/object_vm/gpu_mmu_spec.spl` and `doc/06_spec/03_system/lib/gpu/object_vm/gpu_mmu_spec.md`), as well as the design/contract artifacts (`doc/05_design/gpu_mmu.md`, `.spipe/gpu_mmu/state.md`) and the CPU reference model unit spec (`test/01_unit/lib/gpu/object_vm/object_vm_residency_spec.spl`).

Lane scope complete here:
- Keep tracking evidence in `.spipe/gpu_mmu/state.md` and `doc/03_plan/agent_tasks/gpu_mmu.md`.
- Do not edit this lane file for ongoing feature execution beyond status updates.

Remaining feature work outside this tracking-only lane:
- backend/store and optional-path acceptance coverage in `src/lib/nogc_async_mut/gpu/store` and `src/lib/nogc_async_mut/gpu/placement_backends`,
- implementation-gate evidence rows in `.spipe/gpu_mmu/state.md`.
