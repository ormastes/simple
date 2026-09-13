<!-- codex-architecture -->
# Full Pure-Simple SIMD Bootstrap: TLDR

Purpose: make SIMD one pure-Simple, scalar-defined feature used by compiler, interpreter, database, HTTP, and the exact admitted Stage 4 tools.

## Core decision

`src/lib/common` owns `SimdCapabilities`, `SimdBackend`, `SimdLane<T, N>`, `ScalableSimdLane<T>`, ProcessingIR operations, and scalar semantics. Compiler types and semantics prove legality, MIR stays target-independent, MIR optimization decides profitability, backends encode only admitted operations, and the interpreter evaluates the same operations as deterministic scalar lanes. Database and web code use `DatabaseSimdKernels` and `WebSimdKernels`; they never detect an OS or ISA.

Backend support is per operation. A name counts as implemented only with capability and OS-state detection, lowering, emission, strict rejection, scalar equivalence, and target evidence. Unknown capabilities select scalar. SVE/SVE2/RVV use runtime vector length and predicates; they are never modeled as fixed 128-bit vectors.

## Dispatch and performance

Discovery happens once. An immutable generation caches the capability fingerprint, exact artifact/manifest identity, and backend per kernel family. Hot paths do one table lookup and do not read files/environment, spawn processes, scan trees, or acquire a lock after publication. Explicit test generations provide forced-backend control; strict mode rejects unsupported choices.

ProcessingIR validates bounds, alignment, aliases, masks, tails, and work limits before the CPU executor chooses a backend. Selection finishes before output mutation. Benchmark receipts record the selected backend, correctness hash, latency percentiles, throughput, and RSS.

## Current blockers

- `src/compiler/30.types/simd_platform.spl` is a Linux-text detector with an unsafe SSE2 default and placeholder intrinsic methods.
- `src/lib/nogc_sync_mut/simd/profile.spl` relies on runtime externs and gives scalable tiers nominal 128-bit widths.
- `src/compiler/70.backend/backend/native/isel_x86_64.spl` rejects ordinary SIMD MIR operations.
- RISC-V scalable lowering is explicitly deferred; complete SVE/SVE2 and Wasm paths are not present.
- Existing Rust/C SIMD kernels are comparison/bootstrap evidence, not fulfillment of pure-Simple production ownership.

## Phase evidence

Every phase row binds stage, provenance, executable path/hash, source and manifest identity, isolated roots, supported commands, exact suite command/result/duration, capability/backend identity, retained evidence, and actionable blocked-row ownership. Stage 2/3 evidence is focused; only one unchanged Stage 4 hash can satisfy release and deployment.

Next paths: `doc/05_design/full_pure_simple_simd_bootstrap.md`, `doc/03_plan/sys_test/full_pure_simple_simd_bootstrap.md`, `src/compiler/50.mir`, `src/compiler/60.mir_opt`, `src/compiler/70.backend/backend/native`, `src/compiler/95.interp`, and `src/lib/nogc_sync_mut/simd`.
