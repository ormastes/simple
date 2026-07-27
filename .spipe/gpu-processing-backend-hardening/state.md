# Feature: gpu-processing-backend-hardening

## Raw Request
`$sp_dev harden,and,optimize,fully,utilize,gpu,power,add,a,lot,tests,for,coverage, does,cuda,vulkan,metal,gpu,processable,producing,backend,work,properly`

## Task Type
code-quality

## Refined Goal
Harden and measure the CUDA, Vulkan, and Metal ProcessingIR producers so every supported host proves exact device execution, stable provenance, bounded failure behavior, and evidence-based offload preference without CPU fallback being reported as GPU work.

## Acceptance Criteria
- AC-1: Linux CUDA and Vulkan execute exact ProcessingIR fixtures with positive device provenance and no CPU fallback.
- AC-2: A persistent Linux CUDA daemon session passes three warmups and five measured exact requests with stable provenance and median device, round-trip, and non-device-overhead timing.
- AC-3: CUDA, Vulkan, and Metal reject invalid work and expose typed unavailable, initialization, submit, readback, and mismatch failures.
- AC-4: Offload preference uses measured independent CPU and device time and classifies results below the required speedup as available-not-preferred.
- AC-5: Prepared macOS evidence proves Metal execution and failure behavior; while unavailable, its open TODO names prerequisites, commands, artifacts, owner, and reviewer.
- AC-6: Executable SSpec contracts and operator manuals remain aligned, contain no placeholder passes, and `doc/06_spec` contains no executable specs.
- AC-7: Current-host native evidence, runtime/compiler checks, environment audits, and highest-capability review pass before sync.

## Scope Exclusions
No host-unavailable Metal execution is counted as PASS; no compiler bootstrap is run unless a focused current-host check cannot otherwise be produced.

## Cooperative Review
Lower-model sidecars may inspect disjoint CUDA, Vulkan, and Metal evidence rows. Merge owner: primary Codex session. Final reviewer: highest-capability model. Shared interfaces: `ProcessingCudaExecutor`, `processing_ir_execute_*`, and `SimpleOsGpuHostPlatform`. Manual flow helpers: `step("negotiate processing backend")`, `step("submit exact processing workload")`, and `step("validate device receipt")`. Setup/checker helper: `scripts/check/check-simpleos-gpu-fallback-wire.shs`. Any future placeholder must use `assert(false)` or `fail(...)`. Generated-manual review owner: final reviewer.

## Phase
dev-done

## Log
- dev: Refined the persistent processing-backend hardening goal into seven acceptance criteria.
- impl: Added a strict daemon-wire CUDA mode with three warmups, five measured exact requests, stable provenance, and median device/round-trip/non-device-overhead timing.
- verify: Strict probe/runtime/daemon builds pass and median self-test passes; live device evidence remains open because the final startup-recursion source fix was not rebuilt after the three-cycle cap.
