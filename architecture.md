# Architecture Overview

## Goals (grounded in feature list & language spec)
- Feature work should stay locally scoped: each feature touches parser → compiler → runtime via narrow contracts in `src/common/`.
- Minimize dependency fan-out: no “reach across” into unrelated modules to add a feature from `feature.md`.
- Standardise interfaces (GC, ABI, loader) in `src/common/` so new features don’t create ad-hoc couplings.
- Provide clear contracts for runtime/GC so memory management stays behind a stable boundary while implementing GC-managed default from the spec/feature list.
- Keep watch/build/run predictable and isolated to driver+compiler+loader; adding a language feature should not require touching them.
- Logging should be structured, low-overhead, and opt-in: prefer `tracing` spans/fields over ad-hoc prints. Use `#[tracing::instrument]` on hot paths when diagnostics are needed; avoid pervasive logging in perf-sensitive code paths by default.

## Project Layout (high level)
```
src/
  common/          # Shared interfaces/types; small, stable surface
    - DynModule/DynLoader traits
    - ConfigEnv (config, env vars, args - dict interface)
    - (planned) GcHandle, GcRoot, GcAllocator
  type/            # Type checker/inference crate (HM scaffold, unification)
  parser/          # Syntax + AST; no runtime deps
  compiler/        # Parser -> SMF; depends on parser + common + loader structs
  loader/          # SMF loader; exports DynLoader/DynModule impl
  native_loader/   # OS dynlib loader; same interface
  lib/             # Native stdlib bits (e.g., term IO)
  driver/          # Runner + watcher + dependency cache
  runtime/         # GC wrapper, scheduler (planned), builtin services
  log/             # Logging facade and tracing setup (structured logging)
```

## Dependency Discipline (by feature area)
- **common**: the only place to add new cross-cutting contracts when implementing features from `feature.md` (e.g., effect flags, ABI structs). Depends on nothing else. Includes:
  - `ConfigEnv`: unified dict-like interface for config values, environment variables, and CLI arguments. Used by driver, compiler, and runtime for configuration without creating cross-module dependencies.
- **parser**: implements syntax from the language spec; depends only on stdlib/common types. Adding features like enums, pattern matching, macros should not depend on runtime.
- **compiler**: depends on parser+common. Implements lowering/codegen for features (structs, enums, traits, effects) but talks to runtime only via common ABI (GC handles, call ABI). No direct dependency on runtime internals.
- **loader/native_loader**: implement `DynLoader`/`DynModule`; no dependency on parser/compiler/runtime. Adding dynamic loading features (hot reload) stays here.
- **lib (native stdlib)**: uses native_loader; should not depend on compiler/runtime. For IO or system libs from the feature list, expose small wrappers.
- **driver**: orchestrates compile/load/run/watch; depends on compiler+loaders+lib+common. Never reaches into runtime internals.
- **runtime (planned)**: exposes GC/scheduler/FFI via `src/runtime/gc/` and other submodules; compiler targets only these ABIs.
- **log**: centralizes tracing/log setup. Use `tracing` with `instrument` for structured spans instead of scattered prints. Keeps logging concerns out of business logic.
- **common**: defines shared traits (`DynModule`, `DynLoader`) and will host other stable contracts (GC handles, runtime FFI ABI). Everything else may depend on it; `common` depends on nothing else.
- **parser**: pure front-end; depends only on stdlib. No downstream calls into compiler/runtime.
- **compiler**: depends on parser and common. Emits SMF via loader format structs; should not depend on runtime/GC internals directly—use a GC handle trait from `common`.
- **loader/native_loader**: implement the `DynLoader`/`DynModule` interface; no dependency on parser/compiler/runtime.
- **lib (native stdlib)**: uses native_loader to expose system bindings; avoid reaching into compiler/runtime.
- **driver**: orchestrates compile/load/run/watch; depends on compiler + loaders + lib + common. Does not expose internal compiler/runtime APIs.
- **runtime (planned)**: exposes a minimal ABI (allocation, GC, scheduling) via `src/runtime/gc/` and other submodules; compiler targets that ABI only.

## GC / Memory Management Strategy (from spec: GC-managed default)
- **Wrapper API (planned)** in `src/runtime/gc/`: define handles for GC-managed objects, roots, FFI-safe allocation. This is the single touch-point for GC from compiler/runtime.
- **Backend**: use Abfall behind `runtime/gc/abfall_backend.rs`; no other module depends on Abfall.
- **Interfaces to stabilise in `src/common/`**:
  - `GcHandle<T>` opaque references.
  - `GcRoot` for stack pinning.
  - `GcAllocator` trait (alloc/collect) that compiler targets and runtime implements.
- Compiler codegen emits calls only to the GC ABI in `common`; runtime plugs Abfall in; loaders stay unaware.

## Watch/Build/Run Flow (driver)
- `dependency_cache` parses imports/macros → cache (`target/simple_watch_cache.json`).
- `watcher` uses `notify` to track changes, maps to dependents via cache, triggers rebuild + run via `runner`.
- `runner` calls `CompilerPipeline` → SMF → load with `loader` → execute `main`.
- Each step only touches its immediate neighbors.

## Code Quality Tools

### Test Coverage
Uses `cargo-llvm-cov` for accurate coverage measurement.

```bash
make coverage          # Generate HTML report in target/coverage/html/
make coverage-summary  # Print summary to console
make coverage-lcov     # Generate LCOV format for CI integration
```

Install: `cargo install cargo-llvm-cov`

### Code Duplication Detection
Uses `jscpd` for detecting copy-paste code that should be refactored.

```bash
make duplication       # Generate report in target/duplication/
```

Configuration in `.jscpd.json`:
- Minimum 5 lines / 50 tokens to flag as duplicate
- Ignores test files and target/

Install: `npm install -g jscpd`

### Linting & Formatting
```bash
make lint              # Run clippy with warnings as errors
make lint-fix          # Auto-fix clippy suggestions
make fmt               # Format all code
make fmt-check         # Check formatting (CI-friendly)
```

### Combined Checks
```bash
make check             # fmt-check + lint + test
make check-full        # All checks + coverage + duplication
```

### Additional Tools
```bash
make audit             # Security vulnerability scan (cargo-audit)
make outdated          # Check for outdated dependencies
make unused-deps       # Find unused dependencies (requires nightly)
```

Install all tools: `make install-tools`

## Feature Implementation Guidance (map to feature.md)
- Core syntax/types (basic types, structs/enums/patterns, traits/impl):
  - Parser: grammar only.
  - Compiler: lowering + codegen; if new ABI needed (e.g., trait vtables), define trait/struct in `common`; runtime only consumes ABI.
  - Runtime: optional helpers via small APIs in `common` (e.g., pattern-match helpers).
- Concurrency/actors/effects:
  - Define effect/actor ABI types in `common`.
  - Parser/compiler implement syntax/analysis; runtime implements scheduler behind ABI.
- Memory/pointer types (GC default, unique/shared/weak/handle):
  - Represent pointer semantics in `common` (type markers/ABI); runtime handles implementation; compiler only targets the ABI.
- Stdlib/system features (IO, term, native libs):
  - Isolate in `lib` + loaders; avoid compiler/runtime coupling.
- Avoid cross-module reach: when a feature needs another subsystem, first add a narrow interface in `common` rather than reaching into internals.
- Logging/AOP note: Rust has no runtime AOP; use compile-time weaving via proc-macros like `#[tracing::instrument]` to capture args/latency with minimal boilerplate. Favor span-based, structured logging over stringly prints; keep it opt-in so perf-sensitive paths stay clean.

## Logging Strategy (cross-cutting)
- Use `tracing` for structured, span-based logging; init once via `simple_log::init()` (respects `SIMPLE_LOG`/`RUST_LOG`).
- Use `#[tracing::instrument]` to capture entry/exit/args with minimal overhead—this is the closest to AOP weaving Rust offers.
- Prefer spans with fields (`tracing::info_span!(...)`) over ad-hoc prints; keep logging opt-in for perf-sensitive paths.
- Rust has no runtime AOP; lean on proc-macros and DSL transforms if we need cross-cutting concerns.

## Next Steps
- Flesh out `runtime/gc/` with the Abfall-backed wrapper and put GC traits/types into `common`.
- Expand `CompilerPipeline` to real IR/codegen, still targeting the `common` GC ABI.
- Add CLI entry to watch/run using `driver::watcher::watch`.
