<!-- codex-design -->
# Agent Tasks: Backend Layer Artifact and Runtime Matrix

## Coordination rules

- Isolated worktrees are mandatory; agents do not push directly.
- The main-worktree merge owner is `/root` (highest-capability root agent).
- Final acceptance is performed by the best available normal/highest-capability
  reviewer after all sidecar findings are reconciled.
- Ownership tags use `backend-artifact:<family>:<stage-or-test>`. An agent claims
  the tag in the bug/task ledger before editing; another agent must not fix that
  tagged item concurrently.
- Each lane inventories its whole assigned slice, implements grouped root-cause
  fixes, then runs focused incremental checks. Do not fix one compiler error and
  restart the whole matrix repeatedly.
- Maximum three verify/fix cycles per lane; no repeated green checks.

## Shared interface freeze before fan-out

The primary/highest-capability pass owns and freezes:

- `BackendCapability`
- `BackendArtifactCapabilityRegistry`
- `BackendArtifactAdapter`
- `BackendArtifactCaptureCoordinator`
- `BackendRequestedStageTracker`
- `BackendEnvironmentProfile`
- `BackendEnvironmentProbe`
- `BackendMatrixCellKey`
- `BackendMatrixCellStatus`
- `BackendArtifactMatrixLedger`
- `BackendArtifactMatrixRunner`

It also freezes the scenario `step("...")` names and checker helpers in the
detail design. Any unimplemented SSpec checker must call
`fail("backend artifact oracle not implemented")`.

## Work waves (four total concurrent slots including root)

### Wave 0 — Contract closure and baseline

Owner: root/highest-capability agent. Sidecars: **N/A** until interfaces freeze.

- add capability/ledger/status types and backend-inventory reconciliation;
- add requested-stage completion tracking;
- make current `--debug-dump=all` silent omission an explicit failure;
- complete the real optimized-MIR integration evidence;
- establish fixtures, failure injection facades, and coverage denominator.

This wave is release-blocking and precedes backend parallelism.

### Wave 1 — CPU/native backend adapters

Primary lane: LLVM/llvm-lib adapter, object/link/process receipts.

Sidecar lanes:

- Codex Spark or Claude Haiku: inventory canonical LLVM hook points and existing
  validators only; no broad code generation rewrite.
- Claude Sonnet: Cranelift/native assembly hook inventory and fixture oracle.

Normal/highest-capability owner reviews and implements grouped changes. Owned
tags: `backend-artifact:llvm:*`, `backend-artifact:cranelift:*`, and
`backend-artifact:native-asm:*`.

### Wave 2 — Portable and hardware-source backends

Primary lane: C and Wasm adapters plus execution oracles.

Sidecar lanes:

- lower-model sidecar: Lua/Lean/interpreter/IRTC capability classification;
- lower-model sidecar: VHDL analyze/elaborate/simulate inventory;
- lower-model sidecar: bare-metal x86/AArch64/RISC-V artifact and emulator
  inventory.

Normal/highest-capability owners turn inventories into reviewed adapters and
tests. Tags are scoped by canonical family.

### Wave 3 — Accelerator and graphics-compute backends

Primary lane: shared GPU probe/receipt and deterministic buffer fixture.

Sidecar lanes:

- CUDA/PTX plus HIP;
- OpenCL plus Vulkan/SPIR-V;
- Metal/MSL and macOS runner requirements.

Each sidecar may inventory or draft its narrow adapter/test slice. The primary
owner reviews availability classification carefully: generated-code rejection
or wrong readback is `FAIL`, never `SKIP_UNAVAILABLE`.

### Wave 4 — Environment runners

Primary lane: Linux x86_64 baseline and collect-all/retry runner.

Sidecar lanes:

- Linux AArch64 plus SimpleOS/QEMU AArch64;
- macOS AArch64 plus Metal;
- Windows x86_64, FreeBSD x86_64, and SimpleOS/QEMU RISC-V inventory/scripts.

The FreeBSD lane uses the canonical QEMU bootstrap wrapper from `AGENTS.md`.
Cross-generation evidence does not substitute for required native/emulated run
receipts.

### Wave 5 — Coverage, manual, and final verification

Primary lane: merge owner builds the registry-derived matrix and resolves
cross-lane conflicts.

Sidecar lanes:

- coverage gap inventory by owned module and reachable profile;
- matrix-ledger completeness/staleness audit;
- generated SPipe manual quality and REQ traceability review.

Final reviewer independently checks the `--debug-dump=all` invariant, 95%
reachable branch report, 100% matrix accounting, required environment results,
determinism/integrity, disabled-cost evidence, and zero spec-layout violations.

## Lane deliverables

Every implementation lane returns:

1. claimed ownership tags and exact files changed;
2. registry capabilities and hook points covered;
3. focused parser/unit/integration/environment commands run once;
4. pass/fail/skip/non-applicable cells with receipt paths;
5. branch numerator/denominator and reviewed exclusions;
6. known gaps and whether they block a required profile;
7. one isolated commit hash, with no push.

## Merge order

1. Wave 0 contract closure.
2. CPU/native adapters.
3. Portable/hardware and GPU adapters after rebasing on the contract.
4. Environment runner and ledger integration.
5. Specs/manual/coverage gap fixes.
6. Final highest-capability verification and main-worktree sync/push by root.

## Current implementation handoff

- Contract commit: `e8267a41a80`.
- Shared driver/CLI follow-up: `d223a4913b0`.
- Five shared artifacts have real dynamic evidence through MIR.
- Optimized MIR remains dynamically unconfirmed after timeout.
- All four backend-stage hooks and runtime/device matrix evidence are absent.
- `--debug-dump=all` can currently succeed while silently omitting those four
  requested stages; Wave 0 must fix and test this before any completion claim.
