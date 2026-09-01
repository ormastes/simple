<!-- codex-research -->

# Compiler startup dynload and compile-time gate: local research

Date: 2026-09-01. Inspected commit: `82822944626a6fcc6fbeb1a940437a7419111cf5`.
Scope: compiler/interpreter/loader startup, AOP/plugin/backend attachment, and a
10% compile-time regression gate. This extends, rather than replaces,
`compiler/startup_perf/aspect_dynload_startup_loader_perf_research_2026-08-19.md`.
Sidecars: N/A; this bounded lane was reviewed directly at the normal model tier.

## Current graph and gaps

- `src/compiler/driver/main.spl` looks narrow (two imports), but
  `src/compiler/80.driver/driver.spl` force-imports the pipeline, source/HIR
  pipelines, AOT pipeline and orchestration so interpreter method registration
  works. This makes source-level reachability broader than command intent.
- `CompileContext.create` in `driver_types.spl` constructs only the selected
  concrete backend, which is good, but its module imports still make backend,
  DI, logging and AOP types part of the loaded closure. Verbose mode constructs
  a log aspect; the default constructs an empty `AopWeaver`.
- `driver_pipeline.spl` unconditionally imports `driver_pipeline_aop.*`.
  `weave_aop` correctly returns early when no advice/log rules exist, but all
  AOP parser, conflict, index and MIR-injection modules must already be loaded
  to reach that no-op.
- `plugin_startup.spl` has a sound two-phase idea (index, then activate), yet
  `run_plugin_startup` scans every discovery directory and reads every `.sdn`
  manifest before parsing. Activation is opt-in, so the default task pays for
  discovery that it may never use.
- `driver_pipeline_execution.spl` imports `CodegenPipeline` for JIT/SMF. The
  interpreter path in `driver.spl` uses `InterpreterBackendImpl` directly.
  Compiler, interpreter and loader are therefore conceptually separable but
  not yet separate source/load capsules.
- Existing architecture already defines presence/placement/activation as
  independent axes and a base loader plus optional providers. Existing code
  also has typed `BackendPort`, provider identities and Stage-4 provider symbol
  closure checks. The optimization should complete these boundaries, not add a
  parallel plugin system.
- `test/perf/compiler_runtime.spl` records mean/min/max/stddev with warmups, but
  does not record executable/source/fixture/host identities, cold versus warm
  cache state, median/trimmed mean, coefficient of variation, or baseline
  provenance. A raw mean +10% gate would be noisy and easy to game.

## Essential default closure

The minimal source task needs: fixed CLI routing; config/options normalization;
source collection and signature/import closure; lexer/parser; HIR/type/safety;
diagnostics; and exactly one execution owner. `run/check` selects the reference
interpreter; `compile/native-build` selects MIR, optimizer policy, one backend,
linker and the base loader contract. It does **not** need at startup: VHDL,
CUDA/OpenCL/WASM, non-selected LLVM/Cranelift adapters, AOP implementation when
the summary says no advice can match, block-plugin discovery, profiler/debug
trace/coverage packs, JIT for an SMF with no unresolved generic, or tooling.

The safe boundary is a generated, content-addressed startup plan. It names the
required capability/interface/ABI/provider digest before attachment. Missing,
ambiguous, stale, ABI-incompatible or digest-mismatched providers fail closed;
there is no silent fallback to another backend or to source interpretation.
The base loader retains the old admitted generation until a complete candidate
is validated, so lazy loading does not weaken lifecycle safety.

## Recommended tests and evidence

1. Import-closure snapshots for `--help`, `check`, `run`, `smf`, and
   `native-build`; forbidden optional-module lists make accidental eager imports
   fail.
2. Syscall/load receipts prove root help has no manifest scan/dlopen and a
   no-AOP compile has zero aspect provider activation.
3. Positive selected-provider tests plus missing, wrong digest, wrong ABI,
   duplicate interface, path swap and initialization-failure tests; all must
   fail before publication and retain the prior generation.
4. Semantic parity and byte/fixed-point checks between static and dynamic
   placement for each selected capability.
5. Phase traces record startup, closure, parse, HIR, MIR, optimize, codegen and
   link plus modules/files/bytes, cache result, CPU time and peak RSS.
6. Regression fixture matrix: cold clean CAS, warm no-op, one private-body
   edit, public-signature edit, AOP match-set edit, and native link. Never mix
   these into one average.

## Finding

The highest-confidence immediate win is not changing compiler algorithms. It
is moving optional AOP/plugin/backend implementation imports behind the
existing typed composition boundary, while retaining small summary/index
types in the essential closure. File reads should follow a selected startup
plan; directory discovery must not define the plan.
