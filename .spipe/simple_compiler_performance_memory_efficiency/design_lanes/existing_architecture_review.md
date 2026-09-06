<!-- codex-architecture -->
# Existing architecture review: compiler performance and memory efficiency

## Scope and decision

This review evaluates the tree at the selected baseline, `37bd406e219cc35cae049b4130f5167c21801864`, against the performance/memory program. It is an architecture compatibility review, not proof that any pass is correct or active.

Decision: preserve the numbered compiler architecture and extend its existing optimizer/provider, CollectionPlan, profile, and tool-cache contracts. Supersede the standalone lint frontend and all pass-local duplicate CFG/loop/alias/cost analyses with shared, cached facts. Do not model the program as an app, OS fork, or dynamic plugin required at bootstrap.

## Existing architecture disposition

| Surface | Exact anchors | Decision | Required constraint |
|---|---|---|---|
| Numbered compiler layers | `src/compiler/00.common/`, `10.frontend/`, `20.hir/`, `30.types/`, `35.semantics/`, `50.mir/`, `60.mir_opt/`, `80.driver/`, `85.mdsoc/`, `90.tools/`, `95.interp/`, `99.loader/`; map in `doc/04_architecture/compiler/mdsoc/mdsoc_architecture_tobe.md` | Preserve | Contracts and durable formats rise to `00.common`; typed fact production stays in HIR/types/semantics; MIR facts and transforms stay in `60.mir_opt`; CLI/reporting remains `90.tools`; scheduling/cache ownership remains `80.driver`; runtime evidence bridges through `95.interp`. No sibling-private imports. |
| Optimizer plugin and pass registry | `src/compiler/60.mir_opt/optimizer_plugin.spl`, `optimizer_manifest.spl`, `optimization_passes.spl`, `mir_opt/mod.spl`; `doc/04_architecture/compiler/perf/simple_optimization_plugin.md`; `doc/04_architecture/compiler/optimization/optimization_plugin_jit_hotspot.md` | Preserve and harden | Extend descriptors with implementation status, expectation, invalidation, witnesses and structured result statistics. Keep stable names, required/produced facts, backend policies and fail-closed unresolved `PassKind`. Dynamic providers remain optional and cached outside dispatch. |
| Dynamic manifest ABI | `src/compiler/60.mir_opt/optimizer_manifest.spl` (`simple.opt.mir.v1`, `ManifestPassContract`, `ManifestPassEntry`) | Version, do not mutate v1 incompatibly | A new schema/ABI revision must carry status/expectation/invalidation/remark contract or map omitted v1 fields conservatively to non-transforming/unknown. Never infer `Transform` from an entry symbol. |
| CollectionPlan | `doc/01_research/compiler/collection_planner/collection_plan_ir_2026-07-31.md`; current optimizer in `src/compiler/60.mir_opt/mir_opt/collection_opt.spl`, `_core.spl`, `_patterns.spl` | Adopt as the semantic center; supersede fragmented collection heuristics over time | Extraction follows type/effect completion and precedes ordinary MIR lowering/optimization. One operation registry supplies cost, effects, cardinality, order and uniqueness. Existing COLL codes retain behavior until typed replacements meet compatibility tests. |
| Lint ownership | `src/compiler/35.semantics/lint/collection_patterns.spl`; `src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl`; `src/compiler/90.tools/lint/main.spl` | Supersede the independent parse/AST ownership | `lint_cli_source` currently calls `parse_module_silent_checked` and reconstructs some locations by text scanning. New performance diagnostics consume the compiler session's typed HIR/source map. The CLI becomes an adapter over shared diagnostic results, retaining text-only fallback only when compiler facts are unavailable. |
| Profile formats and runtime bridge | `src/compiler/95.interp/execution/sprof_hotspot_bridge.spl`; `src/compiler/20.hir/hir_lowering/hir_phase_profile.spl`; profile layout loader referenced by the bridge | Preserve `.sprof` compatibility; add versioned optional records | `.sprof-v2` extends rather than replaces function/block/edge evidence. Unknown record kinds must be skippable or version-rejected explicitly. `.sperf` is a separate deterministic compiler summary artifact, not runtime profile state. HIR phase profiling stays opt-in and default-off. |
| Driver/cache ownership | `src/compiler/80.driver/`; `doc/04_architecture/compiler/bootstrap_build_modes.md`; `doc/04_architecture/compiler/00_compiler_architecture.md` | Preserve | `PerfFacts`, `PerfSummary`, analysis receipts and invalidation are per-session/incremental compiler cache products owned/scheduled by the driver, not globals in lint rules or request handlers. Keys include semantic IR hash, imported summary hashes, target/layout, optimization configuration and registry version. |
| MCP/LSP production boundary | `src/app/mcp/main.spl`, `main_dispatch*.spl`; `src/app/simple_lsp_mcp/main.spl`, `tools.spl`; `doc/04_architecture/app/mcp/mcp_performance_regression_enforcement.md`; `mcp_lsp_dap_index.md` | Preserve wrappers and protocol; replace subprocess-per-diagnostic implementation | Production wrappers must execute cached compiled artifacts. MCP/LSP request paths consume a long-lived compiler/query session or cache API. They must not reparse, rescan the repository, reload manifests, rebuild call graphs, or synchronously launch `simple lint` per request. |
| One app / one host | `doc/04_architecture/os/one_app_host_interface_rule.md` | Preserve; program is platform-neutral compiler infrastructure | No per-OS lint/compiler implementation or app fork. Target layout is data. Any runtime counter/file access uses established runtime/host facades; apps and tool servers consume the same compiler service on all OSes. Platform-specific sampling belongs behind a host/runtime capability boundary. |

## Recommended ownership and MDSOC use

Performance analysis crosses HIR, MIR, tooling, profiles and IDE consumers, so MDSOC is suitable for composition and observation, not for relocating the core analyses into `85.mdsoc`.

- Stable shared contracts: `00.common` owns diagnostic/remark categories, confidence, cost-expression wire forms, version identifiers and analysis-incomplete reasons.
- Semantic producers: typed collection/layout/copy/effect facts remain with `20.hir`, `30.types` and `35.semantics` owners.
- Optimization facts and transforms: canonical CFG, dominators, loop forest, def-use, memory versions, scalar evolution and pass receipts belong in `60.mir_opt`.
- Planning and invalidation: `80.driver` composes tiers, budgets, cache keys and preserved/invalidated fact sets.
- Tool adapters: `90.tools` renders lints, remarks, deep reports and `.sperf` comparisons; it must not own a second frontend.
- Runtime evidence: `95.interp` maps versioned `.sprof` evidence to stable profile facts without embedding policy in the file loader.
- `85.mdsoc` may provide a feature capsule/transform that wires optional performance diagnostics, remark sinks and profile attribution into a build. It must not become a sibling-access escape hatch or duplicate domain semantics.

The architecture should define one public compiler-session service, provisionally `PerfFactsService`, with immutable function-scoped results and explicit invalidation receipts. `CollectionPlan`, lint, MIR passes, deep analysis, LSP/MCP and profile correlation consume that service through layer-approved ports. This is preferable to a shared mutable singleton or rule-by-rule visitors.

## Conflicts and supersessions

1. `src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl:57-69` performs text linting and then a fresh checked parse. This conflicts with the shared parsed/typed-program requirement and measured lint latency. Supersede it with a session/result input while preserving a standalone adapter for direct file invocation.
2. The same file reconstructs collection locations through `lint_cli_find_fn_line` and line matching. This conflicts with reliable source-map ownership. Typed diagnostics must carry primary and related spans from HIR/MIR provenance.
3. `src/app/simple_lsp_mcp/tools.spl` launches command-style queries and diagnostics (`run_command_text`, `run_lsp_query`, `run_lsp_diagnostics`). This conflicts with a persistent cached analysis service on the hot request path. Preserve the JSON/MCP surface but route to in-process/session-backed query ports or a persistent daemon.
4. `doc/04_architecture/app/mcp/mcp_lsp_dap_index.md` documents file-level mtime caching, while compiler summaries require semantic dependency and configuration invalidation. Mtime remains an input freshness check, not a sufficient `PerfFacts` cache key.
5. `doc/04_architecture/compiler/perf/simple_optimization_plugin.md` says current passes become static plugins but lacks truthful implementation status and activation expectation. Extend, do not discard, the provider model.
6. `optimizer_manifest.spl` declares itself a skeleton and its v1 contract expresses inputs, outputs and purity but not status, transformation expectation, preservation/invalidation or rejection reporting. A v2 contract is required before external transforming passes can claim conformance.
7. Any existing pass-local loop, alias, reachability, expression-key or def-use reconstruction is superseded after shared facts ship. During migration, adapters may translate shared facts to old APIs; parallel authoritative implementations are forbidden.
8. `.sprof` runtime evidence and proposed `.sperf` static summaries must remain distinct. Profile counts are workload observations; `.sperf` bounds are deterministic compiler claims with assumptions and confidence.

## Startup and hot-path risks

| Risk | Affected path | Required mitigation/evidence |
|---|---|---|
| Parser/compiler process per lint or LSP request | `entry_and_fixes.spl`; `simple_lsp_mcp/tools.spl` | Reuse one parsed/typed session. Measure warm startup and representative diagnostics/query latency on realistic fixtures. |
| Manifest/provider discovery in dispatch | `optimizer_plugin.spl`, `optimizer_manifest.spl` | Load and validate once per session; build immutable stable-name/alias indexes; no filesystem or dynamic-library work in per-function/per-instruction dispatch. |
| Rebuilding graph facts for each pass | `60.mir_opt` analyses and transforms | One function analysis bundle with preservation/invalidation receipts. Verify a pass cannot read a stale fact generation. |
| Unbounded symbolic/interprocedural work | deep analysis and CollectionPlan planning | Tier budgets for function size, SCC size, candidate count, expression depth and solver time. Return `AnalysisIncomplete(reason)` and cache it with dependency/version keys. |
| Profile ingestion contaminates deterministic builds | `.sprof` bridge and planning | Profile is an explicit optimization input and cache-key component; non-PGO builds do not consult ambient profile files. |
| Diagnostics add normal-build noise/cost | `simple check`, LSP | Always-on tier is one near-linear typed-HIR collection pass. Missed optimizations are opt-in remarks, not default warnings. |
| Cache staleness across target or registry changes | compiler driver/cache | Key target triple/layout ABI, language semantics, optimization config, operation-registry version, imported summaries and provider manifest hashes. Publish explainable invalidation receipts. |
| MCP/LSP whole-tree scans or synchronous subprocesses | `src/app/mcp`, `src/app/simple_lsp_mcp` | Follow `mcp_performance_regression_enforcement.md`: compiled wrappers, no raw-source launch, no repeated scans, explicit mutation invalidation, warm-start/request/RSS gates. |
| Host-specific profiler forks | tool/app layers | Put hardware sampling and OS counters behind one optional runtime/host capability. Keep compiler, lint CLI and protocol messages OS-neutral. |

## Documentation that must be created or updated

1. Create `doc/04_architecture/compiler/perf/simple_compiler_performance_memory_efficiency.md` as the canonical layered architecture: owners, public interfaces, tier scheduling, startup/hot paths, cache keys, invalidation and fail-closed rules.
2. Create its one-screen companion `doc/04_architecture/compiler/perf/simple_compiler_performance_memory_efficiency_tldr.md`.
3. Update `doc/04_architecture/compiler/perf/simple_optimization_plugin.md` with `PassStatus`, `PassExpectation`, activation witnesses, result/remark schema, fact preservation/invalidation and effective-pipeline truth.
4. Update or supersede the manifest design referenced by `src/compiler/60.mir_opt/optimizer_manifest.spl` (`doc/05_design/optimizer_manifest_versioned_design.md`) with a compatible v2 migration and v1 conservative mapping.
5. Promote the accepted parts of `doc/01_research/compiler/collection_planner/collection_plan_ir_2026-07-31.md` into architecture/detail design, explicitly naming the operation-registry owner and shared `PerfFactsService` dependency.
6. Update `doc/04_architecture/app/mcp/mcp_lsp_dap_index.md` to distinguish mtime file freshness from semantic summary invalidation and to prohibit subprocess-per-request performance diagnostics.
7. Update `doc/04_architecture/app/mcp/mcp_performance_regression_enforcement.md` with the compiler-session cache, diagnostics latency and max-RSS gates.
8. Add versioned `.sperf` and `.sprof-v2` format designs with compatibility, provenance, deterministic/profile separation and invalidation rules.
9. Add an ADR recording that source lints, optimization remarks and deep/profile findings are distinct user contracts; default lint severity cannot be used to expose ordinary missed transformations.
10. Update `doc/04_architecture/compiler/00_compiler_architecture.md` to link the new architecture and state that tools consume compiler-owned parsed/typed artifacts.

## Design acceptance gates

- No new feature-private parser, CFG, loop detector, alias engine or effect lattice.
- No `Transform` pass without positive/negative witnesses, verification, statistics and explicit preservation/invalidation.
- No unknown/timeout/failure state can authorize movement, elimination, stack promotion, fusion, vectorization or bounds-check removal.
- Default lint remains one shared near-linear HIR fact collection plus indexed rule evaluation.
- MCP/LSP production paths use cached compiled wrappers and a persistent analysis cache; representative warm latency and RSS are verified.
- Profile/static formats are versioned and fail closed; cache invalidation is observable.
- Target/OS differences remain data or established host capabilities, never app/compiler forks.

## Collaboration handoff

- Sidecar lanes: this independent architecture-review lane only; additional lower-model broad-generation lanes are `N/A` for this artifact.
- Merge owner: root SPipe/design agent.
- Final reviewer: root normal/highest-capability design reviewer.
