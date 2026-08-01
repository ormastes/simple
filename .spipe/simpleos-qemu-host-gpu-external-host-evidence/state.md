# SimpleOS QEMU Host-GPU External-Host Evidence

## Raw Request
Make other-host needs into a plan and TODO, postpone them, and identify what remains.

## Task Type
todo

## Refined Goal
Keep Windows DirectX, macOS Metal, and prepared NVIDIA CUDA execution evidence explicitly postponed under existing TODO ownership while local Linux/QEMU and architecture work continues without false completion claims.

## Acceptance Criteria
- AC-1: One plan maps every postponed prepared-host row to its existing TODO instead of creating duplicate tracking entries.
- AC-2: The plan names host prerequisites, canonical commands, required artifacts, resume triggers, and fail-closed acceptance evidence for Windows DirectX, macOS Metal, and NVIDIA CUDA.
- AC-3: Postponed rows remain open and cannot be reported as PASS from source inspection, API names, emulation, screenshots, or cached evidence.
- AC-4: The plan separates external-host work from remaining local/compiler/QEMU work so local progress can continue independently.
- AC-5: No runtime, backend, protocol, direct `rt_*`, WebIR, Draw IR, or Engine2D implementation changes are made by this planning lane.

## Scope Exclusions
- Running hardware evidence without the required host.
- Duplicating the GPU/macOS TODO119 row, TODO544, TODO563, TODO564, TODO569, or TODO570.
- Treating Linux translation/emulation as native DirectX or Metal proof.

## Cooperative Review
- Lower-model audits: DirectX, Metal/CUDA, and fresh-QEMU/compiler lanes completed read-only against current main.
- Merge owner: primary `/root`; workspace paths are intentionally ephemeral.
- Final reviewer: normal/highest-capability Codex review of TODO ownership, exclusions, and remaining-work classification.
- Shared interfaces: `SimpleOsHostGpuSession`, `SimpleOsHostGpuReceipt`, `simpleos_host_gpu_validate_receipt`, `processing_perf_evidence_valid`.
- Manual steps: `Run the ProcessingIR parity fixture`; `Report device-backed host acceleration evidence`.
- Setup/checkers: `simple_binary_is_valid`, `qemu_argv_evidence_valid`.
- Fail-fast placeholder policy: `fail("native host GPU evidence unavailable")`; no placeholder is added by this lane.
- Generated-manual review: N/A because no executable SSpec changes.

## Phase
dev-done

## Log
- dev: Reused existing external-host TODOs and defined a postponed evidence-plan contract without implementation changes.
