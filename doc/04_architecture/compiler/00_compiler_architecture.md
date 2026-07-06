# Compiler Architecture

This is the entrypoint for compiler architecture. Detailed backend, SIMD,
MDSOC, optimization, and graphics-backend documents stay in their topic
folders; this file defines the stable map across them.

## Scope

The compiler owns source parsing, semantic lowering, optimization, backend
selection, artifact emission, and tool-facing query surfaces. Runtime startup,
UI rendering, and test orchestration are separate architecture slices that
consume compiler artifacts but do not own compiler policy.

## Layer Flow

```text
source files
  -> 00.common diagnostics/config/effects
  -> 10.frontend parser + AST + tokens
  -> 15.blocks domain blocks and block adapters
  -> 20.hir / 25.traits / 30.types / 35.semantics
  -> 40.mono monomorphization and template materialization
  -> 50.mir / 55.borrow / 60.mir_opt
  -> 70.backend
       -> C / LLVM / Cranelift / WASM / CUDA / Vulkan / native artifacts
  -> 80.driver
       -> check / build / native-build / package metadata
  -> 90.tools / 95.interp / 99.loader
       -> query, interpreter, module resolver, SMF loader
```

## Ownership

| Area | Owner docs | Notes |
|------|------------|-------|
| MDSOC layers | `compiler/mdsoc/mdsoc_architecture_tobe.md` | Numbered compiler layer map and shared tree-node rules |
| Backend sharing | `compiler/backend/unified_backend_architecture.md` | Shared parser, FFI, and backend interface contracts |
| Bootstrap build modes | `compiler/bootstrap_build_modes.md` | Pure-Simple `dynload`/`one-binary`, Rust seed warning, dependency invalidation |
| Runtime-family backend audit | `compiler/backend/runtime_backend_completion_audit.md` | Facade/runtime-family ownership and smoke evidence |
| Optimization | `compiler/optimization/`, `compiler/perf/` | Compile-time and artifact-size improvement lanes |
| SIMD | `compiler/simd/` | Fixed/scalable vector and strict emit architecture |
| Graphics backend | `compiler/graphics/` | Compiler-owned graphics/backend acceleration boundaries |

## Invariants

- Parser, AST, HIR, MIR, and backend interfaces are shared; backend-specific
  behavior starts after common IR contracts.
- Source position and diagnostic types come from common layers so downstream
  tools report stable file/line/column locations.
- Backend artifacts must carry enough metadata for startup and test runners to
  avoid guessing launch mode, runtime family, target ABI, or dependency needs.
- Normal bootstrap must reuse the Rust seed/runtime and rebuild only
  pure-Simple stages; Rust rebuilds are explicit `--full-bootstrap` work.
- Entry-closure and native cache reuse are conservative around AOP/MDSOC,
  interpreter, loader, and compiler ABI changes.
- Runtime-family restrictions and no-allocation policies must be enforced at
  compiler entrypoints before target-specific native or SimpleOS execution.

## Bootstrap / Interpreter / Loader Boundary

The coordinated refactor lane is
`doc/03_plan/agent_tasks/bootstrap_compiler_interpreter_loader_arch_refactor.md`.
Bootstrap owns staged build policy and cache invalidation, the compiler driver
owns pipeline contracts, the interpreter owns execution/session state, and the
loader owns resolver/SMF materialization. Shared contracts belong in common
compiler layers or explicit facades; sibling layers must not import each
other's private subtrees to shortcut the refactor.

## Related Entrypoints

- Startup: `../startup/00_startup_architecture.md`
- Testing: `../test/00_test_architecture.md`
- UI: `../ui/00_ui_architecture.md`
- Web framework/UI web: `../ui/web/00_web_framework_architecture.md`
