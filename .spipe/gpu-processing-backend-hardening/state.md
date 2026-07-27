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
- verify: The diagnostic probe rebuild passes and proves request 1 has valid correlation/provenance/timing but an 8x wire output. A 217-module isolated daemon build exposed and mapped a trait-erased Engine2D shutdown crash; concrete CUDA/Vulkan/Metal lifecycle dispatch fixes it, and the rebuilt daemon again reaches a valid CUDA receipt. Fresh-cache disassembly then localizes the remaining 8x defect to tagged `[u32]` slots read as unboxed values. A runtime-owned bulk copy+wire-checksum helper replaces the million-iteration Simple loop and passes its focused Rust unit, but runtime/daemon live verification is deferred after the three-cycle cap.
- verify: The incrementally rebuilt CUDA/Vulkan runtime exports the bulk helper, the isolated daemon relinks with `4 compiled, 213 cached, 0 failed`, and the exact device-warm gate passes all three warmups plus five measured 1,048,576-element CUDA requests. Medians are `155110 us` device, `312012 us` round trip, and `156902 us` non-device overhead; every receipt has exact output/checksum, stable positive provenance, and `available-not-preferred` classification against the independent CPU oracle.
