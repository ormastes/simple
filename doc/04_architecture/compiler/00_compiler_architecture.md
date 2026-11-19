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
  -> 20.hir / 25.traits / 30.types / 35.semantics
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
- Runtime-family restrictions and no-allocation policies must be enforced at
  compiler entrypoints before target-specific native or SimpleOS execution.

## Related Entrypoints

- Startup: `../startup/00_startup_architecture.md`
- Testing: `../test/00_test_architecture.md`
- UI: `../ui/00_ui_architecture.md`
- Web framework/UI web: `../ui/web/00_web_framework_architecture.md`


<!-- wave-f-perf-analysis-collection-refactoring-2026-11-19 -->

## Read-Only Performance Analysis Side Tables and Optional Analyzer Boundary

Canonical plan: [Simple Performance Analysis and Collection Refactoring](../../03_plan/compiler/performance_analysis_and_collection_refactoring_2026-11-18.md) (§8, §12.3, §13, §16.2, §19).

- **Read-only semantic facts and immutable side tables:** Typed HIR performance facts (`src/compiler/35.semantics/perf_facts/`) and symbolic cost/idiom/contract records (`src/compiler/35.semantics/perf/perf_analysis_contracts_v1.spl`) operate strictly read-only over revisioned, pseudo-immutable AST/HIR/MIR snapshots. Analysis outputs (`FunctionCostSummaryV1`, `LoopIdiomCandidateV1`, `ResourceContractCheckV1`, `PerfFindingRecordV1`) live in immutable side tables keyed by stable `SymbolId` and `semantic_revision` — never as mutable fields, parent back-pointers, or editor state attached to shared AST/HIR nodes.
- **Target-neutral logical semantics vs backend cost refinement:** Logical collection semantics (`CollectionPlan` in `35.semantics/perf/collection_plan.spl`) and symbolic work/cardinality bounds remain portable above `70.backend`. Backend models (CPU, SIMD, CUDA, ROCm, Vulkan) may refine vector width, memory transfer, launch overhead, and parallel span, or fall back to sequential lowering, without altering language-level evaluation order, error/trap behavior, ownership, or floating-point guarantees (§13.2).
- **Tiered execution (`T0..T4`) and compiler admission gate:** `80.driver` normal compilation reuses `T0` front-end facts only and stays independent of deep analysis plugins and recurrence/AARA solvers (`D12`). `90.tools/lint` owns default `T1` (fast local) and `T2` (compositional interprocedural) execution, projected uniformly to CLI, CI, LSP (`src/lib/nogc_sync_mut/lsp/`), and MCP (`src/app/simple_lsp_mcp/`). No rule enters the normal compiler path without passing the 7-point measured wall-time, CPU, allocation, peak-RSS, cold-cache, feature-off zero-allocation, and bootstrap-stability gate (§8.4).
