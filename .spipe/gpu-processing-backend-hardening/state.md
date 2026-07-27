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
- verify: A current-source Vulkan runtime and 32-module probe pass exact 64-value device readback plus unavailable/init/submit/readback/mismatch isolation. The live probe exposed runtime-returned text collapsing the selected-device hash to sentinel `1`; selected-device fingerprinting now remains in the Vulkan runtime owner. The final six-process gate passes with stable RTX A6000 identity/handle `666008366`, while every injected failure retains zero provenance. The compatibility export, runtime registry, codegen table, and interpreter registration compile together.
- verify: The Vulkan wrapper now adds one bounded same-process success/failure/success sequence. It first records 64 exact values with identity `666008366`, arms a submit fault and receives zero provenance, then clears the fault through the canonical environment facade and returns the same exact values and identity without exiting.
- impl: The macOS Vulkan live harness now emits a canonical 64-value ProcessingIR device-readback receipt with fixed checksum `1082179840`, positive handle/identity, zero mismatches, and no CPU fallback; the checker rejects any deviation. Metal fault children are bounded to 30 seconds and 4 MiB, with timeout markers restricted to actual runtime timeout stderr.
- verify: Linux source contracts passed for Vulkan ProcessingIR (5/5) and the Metal live fault spec remains explicitly pending on non-macOS. The fallback contract exposed and repaired missing backend/stage/exit fields in backend-create failures; its final rerun is deferred after the mandatory three-cycle cap. Prepared macOS Vulkan/Metal runtime evidence remains open.
- verify: The repaired macOS failure/fallback source contract now passes 5/5 on Linux. The native CLI `73` promotion spec requires hash-bound non-seed producer/runtime artifacts, the exact no-stub Stage4 profile, stale-output deletion, and 10-minute/16-MiB bounded children; its host-independent contract passes, and the live example is not registered until every prepared input is supplied.
- diagnose: The deployed pure-Simple worker predates `rt_transient_array_scope_begin`. A bootstrap-seed incremental compiler producer cleared that boundary but made no retained log or cache progress after source diagnostics, so the attempt was terminated under the no-progress guard. The retained log proves termination but does not preserve CPU/elapsed telemetry. No driver or `73`/`84` receipt was produced.
- optimize: The failed producer path emitted 13,683 non-fatal common-mistake hints. The bounded `73` promotion probe now enables the existing `SIMPLE_NO_DEPRECATED_WARNINGS=1` path for both producer and driver children, preserving error hints while avoiding that formatting and process-output overhead; the focused contract passes 1/1. A live prepared-input receipt remains open.
