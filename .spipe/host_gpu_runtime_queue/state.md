# Feature: host-gpu-runtime-queue

## Raw Request
with spipe skill, impl all the planed, check event flow and fix any problems. and check them with vulkan, metal, cuda/hip as possible as or make win, mac plan. fix them you think missing for complete and production level gui web 2d engine layers api. make small task apply to spark and verify works with normal llm. make pherallel agent plan and do works in pherallel go

## Task Type
feature

## Refined Goal
Make host/GPU lane markers and Engine2D Draw IR paths emit verifiable runtime queue packets with typed drain/readback evidence, while documenting and testing the remaining production browser-frame/backend gaps.

## Acceptance Criteria
- AC-1: Interpreted and forced-native `target.later(...) gpu` fixtures record begin/end lane counters and exactly one runtime queue packet.
- AC-2: Engine2D exposes public submit and drain result helpers that wrap `rt_host_gpu_queue_*` without direct raw-counter assertions in new SPipe specs.
- AC-3: A GPU-selected `DrawIrBatch` can flow through `DrawIrBatch -> runtime queue submit -> Engine2D render -> runtime drain` with an executable spec and generated manual.
- AC-4: Vulkan and CUDA readback evidence are rerun when available on the local host; Metal and ROCm/HIP produce typed unavailable evidence or a concrete Mac/AMD follow-up plan.
- AC-5: Documentation separates evidence adapters, runtime queue emission, backend readback fixtures, and the remaining production GUI/web browser-frame queue-drain integration.
- AC-6: Spark and normal-model reviews identify unresolved correctness/performance gaps, and those gaps are reflected in the plan/docs.
- AC-7: The feature is not considered production-complete until browser-frame render paths surface queue submit/drain/readback receipts, queue capacity semantics match across Rust/C runtimes, in-flight `SUBMITTED` status is observable, and lane end accounting is exception-safe.

## Scope Exclusions
Full browser-frame GPU rendering, real backend-handle propagation, and cross-host Metal/ROCm hardware validation remain open unless implemented and verified by later SPipe phases.

## Phase
dev-done

## Log
- dev: Created state file with 7 acceptance criteria (type: feature).
- impl: Added focused BrowserBackend runtime queue diagnostics coverage for
  GPU-selected frames and cache-hit reset. Remaining production blockers are
  real backend-handle propagation and backend submit/readback receipts.
- impl: Added runtime submit/complete phase APIs so `SUBMITTED` is observable
  before terminal completion, with Rust runtime and SPipe event-path coverage.
- impl: Split Engine2D runtime queue identity from backend-handle identity,
  changed Simple drain evidence to read `rt_host_gpu_queue_last_backend_handle()`,
  and made the production GUI/web wrapper run the BrowserBackend frame probe
  while keeping same-frame backend readback fail-closed.
