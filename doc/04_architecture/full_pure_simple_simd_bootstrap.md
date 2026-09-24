<!-- codex-architecture -->
# Architecture: Full Pure-Simple SIMD Bootstrap

Status: Accepted for implementation

Requirements: `doc/02_requirements/feature/full_pure_simple_simd_bootstrap.md` and `doc/02_requirements/nfr/full_pure_simple_simd_bootstrap.md`

## Purpose

This architecture makes portable SIMD a pure-Simple compiler and library feature, applies it to database and HTTP hot paths, and binds its verification to the exact four-stage bootstrap artifact. The public behavior is one scalar-defined API. Hardware backends are replaceable accelerators whose legality and results are proved against that definition.

The selected program is intentionally broader than the SIMD code that exists today. Current source contains useful fixed-vector types, MIR operations, auto-vectorization recipes, capability probes, x86/Arm encoders, library dispatch helpers, and scalar reference functions. It also contains overlapping authorities and incomplete paths. In particular:

- `src/compiler/30.types/simd_platform.spl` parses `/proc/cpuinfo`, defaults unknown hosts to SSE2, and contains scalar implementations described as intrinsic placeholders.
- `src/compiler/30.types/simd_capabilities.spl` has fine-grained CPUID, HWCAP, sysctl, and RISC-V probe adapters, but it is separate from the public library profile.
- `src/lib/nogc_sync_mut/simd/profile.spl` obtains a coarse tier from `rt_simd_*` externs; scalable tiers currently report a nominal width of 128 bits.
- `src/compiler/50.mir/mir_instruction_kinds.spl` contains concrete fixed-width SIMD instructions, while `ScalableVecFence` is only a boundary marker.
- `src/compiler/70.backend/backend/native/isel_x86_64.spl` currently rejects ordinary SIMD MIR instructions. Existing `x86_64_simd.spl` and `x86_64_avx512.spl` encoders therefore do not prove an end-to-end native path.
- `src/compiler/70.backend/backend/native/isel_riscv64.spl` explicitly diagnoses scalable-vector lowering as deferred.
- `src/lib/common/simd_lane_pure.spl` supplies exact scalar twins, including 512-bit-width mask and lane semantics, but it is not yet the common contract used by all callers.

These facts are implementation inputs, not exceptions to the requirements.

## Decisions

### One contract and three authorities

`common` owns value semantics and serializable identities. The compiler owns legality and lowering. The host capability boundary owns detection. No application, database, HTTP, MCP, or LSP module may detect an ISA, import an ISA encoder, parse host files, or call a platform runtime symbol.

The frozen public names are:

- `SimdCapabilities`: immutable detected and admitted capability facts.
- `SimdBackend`: stable identity: `scalar`, `x86_64_sse2`, `x86_64_ssse3`, `x86_64_sse41`, `x86_64_avx`, `x86_64_avx2`, `x86_64_avx512`, `aarch64_neon`, `aarch64_sve`, `aarch64_sve2`, `riscv64_rvv`, or `wasm128`.
- `SimdLane<T, N>`: fixed-width logical vector with scalar-defined semantics.
- `ScalableSimdLane<T>`: vector-length-agnostic logical vector used only in strip-mined loops.
- `ProcessingIR`: the common validated processing request. It gains CPU SIMD kernel operations only when their scalar semantics, bounds, and alias rules are expressible in the common IR.
- `DatabaseSimdKernels` and `WebSimdKernels`: platform-neutral adapters from product data to common kernel requests.

`src/lib/common` owns these contracts. Mutable dispatch state belongs in the appropriate `nogc_sync_mut` owner. The existing `src/lib/common/processing/processing_ir.spl` remains the shared processing envelope; SIMD does not create a second application IR.

### Capability discovery and admission

Detection and admission are separate:

1. A platform adapter returns raw feature facts and required OS-state facts.
2. `SimdCapabilities` validates implications and records a capability fingerprint.
3. The compiler/runtime intersects detected facts with the operations actually implemented by the exact artifact.
4. Policy chooses the best legal `SimdBackend` for a kernel.
5. Strict test mode rejects an unavailable or unimplemented forced backend. Production mode selects the next legal backend and ultimately scalar.

For x86, AVX requires CPUID AVX, OSXSAVE, and XCR0 XMM/YMM state. AVX-512 requires AVX plus AVX-512F and XCR0 opmask/ZMM state. Each operation also requires its own subsets, such as AVX-512BW for byte comparisons. AVX-512F alone must not advertise byte-kernel legality. Arm uses OS-provided HWCAP/HWCAP2 facts; Apple Arm must keep SVE/SVE2 false until the platform exposes an admitted facility. RISC-V V requires both architectural availability and a safe vector-length query. Wasm SIMD128 is a target/module capability, not a host CPU guess.

The authoritative pure-Simple capability layer replaces the broad default behavior in `simd_platform.spl`. An unknown probe result admits scalar only. Low-level externs may remain behind one HAL adapter during bootstrap, but their result is typed data; they are not product dependencies and contain no dispatch policy.

### Cached dispatch and invalidation

Capability discovery runs once per process before the first SIMD kernel selection. A thread-safe cache stores:

- capability fingerprint;
- exact artifact SHA-256 and implementation-manifest version;
- selected backend per kernel family;
- forced-test policy, when present;
- generation number.

Hot calls perform one generation check and an indexed/table dispatch. They do not read environment variables, `/proc`, config files, the repository, or spawn processes. MCP startup may initialize the cache eagerly after argument/config parsing; otherwise the first library call initializes it lazily. MCP requests reuse the same immutable generation.

Invalidation is explicit. Tests may install a scoped forced capability set before initialization and restore it by advancing the generation. A changed host configuration, artifact identity, or implementation manifest creates a new process or explicit test generation. File mtimes and request traffic never invalidate SIMD dispatch. This satisfies deterministic caching while preventing test overrides from weakening production checks.

### Fixed and scalable vectors

`SimdLane<T, N>` has a compile-time element type and lane count. Legal element types, lane counts, alignment, mask widths, overflow, shifts, comparison ordering, NaN behavior, and alias rules are checked before MIR generation. Masks are logical lane booleans in common IR; a backend may lower them to x86 k-registers, vector sign bits, Arm predicates, RVV v0, or scalar booleans without changing observable semantics.

`ScalableSimdLane<T>` never exposes a numeric lane count in the source type. It is legal only inside a strip-mined region with explicit active-lane predicates. The loop shape is:

1. obtain the backend vector length for `T`;
2. create a predicate for `index < length`;
3. perform masked loads and operations;
4. perform masked stores or reductions;
5. advance by the returned active vector length.

No code may model SVE, SVE2, or RVV as a fixed 128-bit vector. Fixed-width fallback decomposes into smaller fixed vectors or scalar lanes. Scalable fallback executes the same predicated region through scalar active lanes.

### Legality before profitability

The compiler represents vectorization decisions with a target-independent recipe. A recipe records operation, element semantics, fixed/scalable shape, mask/tail policy, alignment, alias proof, overflow mode, floating-point mode, and required capabilities.

Legality rejects a recipe when any of these cannot be proved:

- memory bounds for every active lane;
- safe behavior for unaligned addresses;
- non-overlap, or an operation-defined overlap direction;
- identical integer wrapping/trapping and shift masking;
- identical comparison and mask semantics;
- the selected floating-point reassociation, NaN, signed-zero, and FMA contract;
- a bounded scalar or masked tail;
- all backend and OS-state capabilities.

Profitability runs only after legality. It uses kernel size, trip count, alignment, expected selectivity, dispatch cost, vector transition cost, and benchmark evidence. A rejected profitability decision retains scalar MIR without changing semantics.

### Lowering pipeline

The compiler uses one direction of dependency:

```text
source/library kernel request
  -> HIR typed vector operation
  -> target-independent MIR vector recipe
  -> legality proof + scalar oracle identity
  -> profitability decision
  -> backend selection from admitted capabilities
  -> fixed or scalable machine operation
  -> encoder / wasm emitter
```

Frontend grammar and vector types remain single-source. `30.types` validates `SimdLane` and `ScalableSimdLane`; `35.semantics` checks operation and mask legality; `50.mir` owns target-neutral instructions; `60.mir_opt` performs vectorization and predication transforms; `70.backend` selects and encodes; `95.interp` executes the scalar definition of the same MIR operation.

The interpreter is the semantic oracle, not a hardware simulator. It accepts all legal portable operations and evaluates active lanes in deterministic scalar order. It rejects backend-specific encoder operations that escaped target lowering. Native backends must never implement language semantics unavailable to the interpreter.

Each backend has an operation manifest. A backend name is implemented only when its required capability probe, lowering, encoder/emitter, strict negative gate, scalar-equivalence gate, and retained target evidence all exist. Partial AVX-512, SVE/SVE2, RVV, or SIMD128 code remains operation-specific and cannot promote an entire backend family.

### ProcessingIR, database, and web integration

`DatabaseSimdKernels` initially maps scan/filter/compare/hash/encoding operations to bounded ProcessingIR requests. `WebSimdKernels` maps ASCII classification, delimiter search, header-name comparison, routing-prefix comparison, UTF-8 validation, and encoding operations. Both expose scalar entry points with identical result formats and correctness hashes.

ProcessingIR validation owns buffer lengths, element format, offsets, overlap, maximum work, and operation identity. The CPU executor selects a legal SIMD backend once per operation family and handles scalar tails. Database and web code sees only the common adapter and cannot branch on OS or ISA. Kernel rollout requires measured end-to-end benefit; a locally faster kernel that misses the selected 20% workload target stays available but is not enabled by default for that workload.

### MDSOC structure

Portable SIMD crosses types, semantics, MIR, optimization, backends, interpreter, libraries, and applications, so it is a virtual capsule under `src/compiler/85.mdsoc/feature/optimization`. The capsule contains feature metadata and transform registration, not copies of backend logic. Target-specific encoders remain private to `70.backend`; raw host probes remain private to the HAL owner; common contracts remain above sibling layers.

The feature transform may introduce vector recipes only through the legality API. Runtime backend selection is an adapter selected from immutable capability data. This preserves the rule that sibling compiler layers communicate through common or next-layer contracts rather than private subtrees.

## Startup and hot-path budgets

Capability discovery is bounded to one initialization and one implementation-manifest validation. It must add no measurable regression to the locked warm MCP startup profile and keep total maximum RSS growth within NFR-SIMD-005. A representative hot kernel performs no allocation after caller-provided output storage is available, no file or environment read, no lock acquisition after cache publication, no process execution, and no full-tree scan.

Observability records artifact hash, capability fingerprint, dispatch generation, requested and selected backend, fallback reason, kernel identity, element count, scalar-tail count, correctness hash, duration, and maximum RSS in benchmark/verification mode. Normal MCP responses do not expose diagnostics unless requested through the existing debug/metrics path.

## Failure behavior

- Unknown, contradictory, or incomplete capability facts admit scalar.
- A forced unsupported backend returns a typed strict-mode diagnostic before execution.
- An unimplemented operation for a detected backend selects a lower implemented operation backend in production and fails in strict verification mode.
- Invalid masks, shapes, bounds, aliases, or scalable-loop construction fail compilation or ProcessingIR validation.
- Backend execution cannot retry through a different ISA after beginning writes. Selection occurs before mutation.
- A phase artifact or receipt mismatch blocks promotion; it cannot be repaired by substituting the Rust seed, a stale binary, or raw-source execution.

## Phase verification interfaces

Every phase row uses `PhaseVerificationReceiptV1` with:

- stage and provenance;
- exact executable path and SHA-256;
- source revision and implementation-manifest fingerprint;
- supported command/capability set;
- isolated cache and output roots;
- component/suite identity and exact command;
- start/end time, duration, exit status, and result;
- selected SIMD backend and capability fingerprint when applicable;
- retained stdout/stderr/evidence path;
- blocker owner, prerequisite, reviewer, and exact resume command for unavailable rows.

The matrix contains compiler check/test/doctest, interpreter conformance, MCP, Simple LSP MCP, SPipe/SSpec, DevHub, and LLM Caret rows for every admitted phase. Stage 2/3 rows run only receipt-admitted supported checks and cannot count as release evidence. Stage 4 runs every applicable suite against one unchanged hash. A failing row prevents the next phase. An unsupported row is a typed retained state, never a pass.

The system-test helpers frozen by the agent plan are `step_detect_simd_capabilities`, `step_run_scalar_oracle`, `step_run_simd_backend`, `step_compare_database_results`, `step_compare_web_results`, `step_bootstrap_platform_handoff_readiness`, and `step_verify_deployed_tools`. Setup/checker helpers are `setup_simd_fixture`, `setup_database_fixture`, `setup_web_fixture`, `setup_phase_suite_fixture`, `check_simd_equivalence`, `check_simd_performance`, `check_bootstrap_candidate`, `check_phase_component_suites`, and `check_deployed_simple_mcp`. Until implemented, each helper fails explicitly.

## Verification gates

Implementation is accepted only when evidence proves:

1. fixed and scalable scalar conformance for lane boundaries, empty inputs, unaligned inputs, aliases, masks, tails, overflow, shifts, comparisons, and floating-point edge cases;
2. strict forced-backend rejection before unsupported instruction execution;
3. per-operation native emission and execution on every claimed backend, with unavailable physical hosts retained as blocked rows and emulation clearly labeled;
4. interpreter/native equality and ProcessingIR CPU-executor equality;
5. database and HTTP correctness hashes plus NFR-SIMD-001 through NFR-SIMD-007 measurements;
6. direct environment/process guard checks for application and library leaves;
7. the phase matrix and exact Stage 4 bootstrap/deployment receipts;
8. compiler, library, MCP, LSP MCP, integration, native smoke, SPipe, full release-bound tests, and `STATUS: PASS` once for the unchanged candidate.

## Requirement trace

| Requirements | Architectural owner |
|---|---|
| REQ-SIMD-001, 004 | Common scalar semantics, fixed/scalable contracts, legality |
| REQ-SIMD-002, 003 | Capability admission, backend manifests, strict gates |
| REQ-SIMD-005, 006 | ProcessingIR plus database/web adapters |
| REQ-SIMD-007 | Common/compiler/library ownership and HAL isolation |
| REQ-SIMD-008, 009 | Exact Stage 4 artifact and deployment receipts |
| REQ-SIMD-010, 011, 012 | `PhaseVerificationReceiptV1` and phase matrix |
| REQ-SIMD-013 | Architecture, design, executable/manual evidence contracts |
| REQ-SIMD-014 | Immutable final evidence, verification, linear sync |

## Consequences and current blockers

The design removes duplicate dispatch policy and makes claims operation-specific and falsifiable. It also requires implementation work before the selected requirements can pass. The current `/proc/cpuinfo` fallback, runtime-extern profile, nominal scalable widths, native x86 SIMD rejection, deferred RVV lowering, and absent complete SVE/SVE2/Wasm paths are blockers rather than accepted fallbacks. Existing Rust/C SIMD kernels may serve as bootstrap comparison evidence, but they do not satisfy the pure-Simple production ownership requirement.

## References

- `doc/04_architecture/compiler/simd/simd_unified_architecture.md`
- `doc/04_architecture/compiler/simd/simd_backend_strict_emit.md`
- `doc/04_architecture/compiler/backend/processing_backend.md`
- `doc/05_design/compiler/simd/simd_rollout_plan.md`
- `doc/05_design/compiler/simd/simd_test_catalog.md`
- `src/lib/common/processing/processing_ir.spl`
- `src/compiler/85.mdsoc/feature/optimization/simd_provider.spl`

