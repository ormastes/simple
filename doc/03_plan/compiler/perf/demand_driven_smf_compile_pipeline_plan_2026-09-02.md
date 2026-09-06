# Plan — Demand-Driven SMF Compile Pipeline

**Parent program:** `doc/03_plan/compiler/perf/compiler_interpreter_performance_program_2026-08-10.md`

This plan is the package/SMF/import/file-I/O implementation expansion of that main compiler performance program and does not replace its startup, interpreter, JIT, or verification work.

## Current status — 2026-09-02 completion audit

**STATUS: FAIL / NOT READY FOR CUTOVER.** The D0-D14 implementation created substantial production structure, but current evidence does not prove the pipeline complete. Both umbrella evidence wrappers and their static mutation guard now exist. Static traceability can pass, while all 35 functional/phase/stop scenarios and all 13 performance/parent-gate scenarios remain fail-closed until admitted runtime or measured receipts exist.

Classification summary:

- Requirements: **0 PROVEN, 18 PARTIAL, 2 MISSING**.
- NFRs: **0 PROVEN, 0 PARTIAL, 6 MISSING** (no admitted measurements).
- Phases: **0 PROVEN, 9 PARTIAL, 1 MISSING** (Phase 9 cutover).
- Stop gates: **0 PROVEN, 5 PARTIAL, 0 MISSING**.
- Parent gates F/S/V/A/Q/J/R: **0 PROVEN, 5 PARTIAL, 2 MISSING**.

Highest-priority blockers are dirty-only and mixed clean/dirty MIR authority, production runtime/std SMF precompilation, route-wide cleanup of pinned capabilities, end-to-end shared pipeline routing including IDE/background optimizer, and retained production-derived evidence. Static umbrella coverage is owned by `scripts/check/check-demand-driven-smf-evidence-static.shs`; it does not promote runtime, performance, native, phase, stop, or parent rows. See `build/review/demand_driven_smf_compile_pipeline_completion_audit_2026-09-02.md` for the requirement-by-requirement audit.

## Phase 0 — Evidence and interface freeze

- Add phase timers and source-open/section-read/action counters.
- Freeze the six core interfaces from detail design.
- Establish matched Go/Simple fixtures and cold/warm baselines.

## Phase 1 — SMF package/class archives

- Define sectioned `SmfPackageIndexV1` and versioning.
- Serialize exports, types, dependency edges, generic bodies, HIR summaries, MIR/object chunks, and receipts.
- Add partial-map readers and corruption/version mutation tests.

## Phase 2 — Go-compatible package command behavior

- Resolve nearest `simple.sdn` for no-argument build/check/run/test.
- Preserve explicit file and `--source` behavior.
- Add `./...` explicit recursive package selection.
- Eliminate implicit recursive scans from warm paths.

## Phase 3 — Shared artifact-service library

- Extract daemon queue, compatibility, leases, cancellation, framed stdio, diagnostics, and lifecycle into a library.
- Adapt compiler daemon and test-runner daemon as profiles.
- Add crash/restart/concurrent-client tests proving CAS authority.

## Phase 4 — Ninja-like action graph

- Persist package/action edges and command identities.
- Add dynamic import edges, SCC scheduling, pools, single-flight, memory budgets, and semantic restat.
- Prove deterministic output under parallel scheduling and cancellation.

## Phase 5 — Lazy imports and HIR demand

- Implement bounded head scanner and verified SMF metadata proxies.
- Implement materialization state machine and promise/task suspension.
- Add deferred HIR bodies and `HirDemandSetV1`.
- Add MIR admission proof and mutation tests rejecting unresolved proxies.

## Phase 6 — Development and promotion backends

- Return cached bytecode or Cranelift baseline synchronously.
- Precompile runtime/std packages as SMFs.
  - Structural implementation: canonical `simple.runtime`/`simple.std`
    `PackageImageV1` identities, action-graph result admission, sealed atomic CAS
    publication, and fail-closed demand-baseline loading live in
    `src/compiler/80.driver/smf/runtime_std_package_set.spl`. Runtime execution
    evidence remains required before REQ-012 is marked proven.
- Run LLVM/native optimization asynchronously with compatible publication.
- Add backend parity and background-failure isolation tests.

## Phase 7 — Generic shape sharing

- Define `LayoutShapeId` and operation dictionaries.
- Reuse baseline bodies by shape.
- Add explicit/profile-guided specialization and cache accounting.
- Measure code size, compile time, and runtime break-even.

## Phase 8 — Async I/O and parser acceleration

- Make common Simple file reads asynchronous-first through `ReadOnlyFileViewV1` and `FileReadPolicyV1`.
- Implement default `auto_map`, strict `must_map`, fallback-capable `prefer_map`, and forced `buffered` policies.
- Add read-only whole-file/bounded-window mapping adapters for supported hosts and an asynchronous buffered/read-ahead fallback for every host.
- Prove identical bounded range, snapshot identity, no-follow, cancellation, short-read, truncation, and error semantics across both transports.
- Add async file/stdio adapters beneath synchronous-looking source semantics.
- Add SIMD lexical scanning behind capability dispatch.
- Benchmark GPU parsing including transfer/dispatch; keep notification-only unless admitted.

## Phase 9 — Cutover and verification

- Route CLI, test, MCP/LSP, and IDE compilation through the same pipeline.
- Run 44 package-index scenarios plus new lazy-materialization and daemon scenarios.
- Verify warm zero-source-open behavior and performance targets.
- Remove legacy scan/daemon/cache paths only after production evidence and one compatibility release.

## Stop gates

- Any unresolved proxy reaching MIR blocks cutover.
- Any daemon-dependent correctness blocks cutover.
- Any warm recursive scan blocks cutover.
- Any background artifact published under a mismatched semantic identity blocks cutover.
- GPU default remains prohibited without transfer-inclusive crossover evidence.
