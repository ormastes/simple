# Local Research — Demand-Driven SMF Compile Pipeline Implementation Gap

**Date:** 2026-09-02
**Scope:** Read-only comparison of the five selected requirements, architecture, design, and plan documents against current production call chains.
**Sidecars:** N/A; no agent-launch tool was callable in this session.
**Production edits:** None.

## Documents reviewed

- `doc/02_requirements/feature/demand_driven_smf_compile_pipeline.md`
- `doc/04_architecture/compiler/perf/demand_driven_smf_compile_pipeline.md`
- `doc/05_design/compiler/perf/demand_driven_smf_compile_pipeline.md`
- `doc/03_plan/compiler/perf/demand_driven_smf_compile_pipeline_plan_2026-09-02.md`
- `doc/03_plan/compiler/perf/compiler_interpreter_performance_program_2026-08-10.md`

No exact demand-driven feature entry was found in `doc/00_llm_process/knowledge_registry.sdn`; the compiler/driver lane therefore remains `mdsoc_only` under repository policy.

## Current production call chain

1. CLI commands call `compiler_entrypoint_admit_v1()` in `src/app/compiler_entrypoint/admission.spl`.
2. Admission refreshes Git/filesystem events, acquires an immutable SCV snapshot, reads the current package index, and exports snapshot/index authority.
3. `Driver.load_sources()` in `src/compiler/80.driver/driver_source_pipeline_loading.spl` calls `package_index_route_current_v1()` unless explicit cold initialization is enabled.
4. `package_index_route_current_v1()` validates SCV/index identity, computes module closure, invalidates reverse dependencies, consumes deterministic SCC order, and selects frozen source paths or verified interface/action archive paths.
5. The driver exports archive paths through `SIMPLE_PACKAGE_INDEX_INTERFACE_ARCHIVES` and `SIMPLE_PACKAGE_INDEX_ACTION_ARCHIVES`.
6. The compiler does not ingest those archives. An archive-only route is explicitly rejected with `archive ingestion is unavailable`; dirty routes continue through normal source parsing, HIR lowering, MIR lowering, and selected native backend.
7. Native backend selection supports LLVM/LLVM-lib and Cranelift in the existing AOT driver. Interpreter tiering and hotspot JIT exist separately under `src/compiler/95.interp/execution`, but are not driven by the package action graph or SMF demand identity.

## Document-to-code comparison

| Required capability | Current evidence | Status |
|---|---|---|
| Immutable SCV snapshot and event-maintained inventory | `src/app/compiler_entrypoint/{admission,inventory_events}.spl`, `src/lib/scv/{compile_snapshot,compile_source_inventory}.spl` | Implemented structurally |
| Persistent package/import/reverse-import/SCC index | `src/compiler/80.driver/cache/package_module_index.spl` | Implemented structurally |
| Deterministic package/SCC scheduling | `package_scc_scheduler.spl` is consumed by `package_index_route.spl` | Partial: ordering exists, reusable worker/action service does not |
| Typed TLDR/SMF metadata and early cutoff | `package_tldr_metadata.spl` defines headers, sections, keys, admission, and cutoff | Partial: metadata utilities are not the frontend semantic authority |
| Sealed package archives | `package_archive_cache.spl` validates and publishes interface/action files | Partial: paths are routed but archive contents are not consumed by compiler phases |
| Warm zero-source-open compilation | Clean archive-only routes are rejected in `driver_source_pipeline_loading.spl` | Missing |
| `SmfPackageIndexV1` section directory and lazy section reads | Only a compatibility alias exists; no production section-index reader is connected to imports | Missing |
| Bounded source-head import discovery | Native closure has a lightweight import scanner, but no canonical bounded-head-to-SMF cold metadata pipeline | Partial/non-authoritative |
| Import metadata proxies and single-flight materialization | `ImportMaterializationV1` and its state machine have zero production definitions | Missing |
| Demand-driven semantic/HIR bodies | `HirDemandSetV1` has zero production definitions; current driver lowers loaded sources through ordinary HIR flow | Missing |
| MIR closed-set admission proof | `MirAdmissionV1` has zero production definitions; existing checks do not prove absence of all deferred proxies | Missing |
| Shared artifact service | `ArtifactServiceProfileV1` and `BuildActionV1` have zero production definitions | Missing |
| Persisted dynamic action graph, cancellation, budgets, single-flight | Cache indexes and SCC helpers exist, but no common coordinator/worker execution graph consumes them | Missing |
| Development baseline bytecode/Cranelift | Cranelift AOT and interpreter/JIT components exist | Partial: no package-demand synchronous baseline contract |
| Asynchronous LLVM promotion | Promotion receipt/cache helpers exist, but no snapshot-bound background compile queue publishes LLVM upgrades | Missing |
| Runtime/std precompiled SMFs | No demonstrated production package archive cutover for runtime/std | Missing |
| Generic ABI/layout shape sharing | `LayoutShapeId` and dictionary-based shared baseline bodies have zero production definitions | Missing |
| Async mapped/buffered common file view | `FileReadPolicyV1` and `ReadOnlyFileViewV1` have zero production definitions | Missing |
| CLI/test/MCP/LSP common cutover | Entry admission is routed broadly | Partial: downstream compilation still lacks archive/demand execution |
| Benchmark counters and matched Go/Simple evidence | Existing phase logs and separate performance plans exist | Missing for the specified source-open, section-read, action, and demand counters |

## Ranked performance blockers

### P0 — Archive ingestion is absent

**Impact:** Highest. A clean package cannot bypass parsing, semantic analysis, HIR, MIR, and code generation because the driver only exports archive filenames and then rejects an archive-only route.

**Concrete owner:** Compiler driver/frontend integration owner. Primary files: `driver_source_pipeline_loading.spl`, a new compiler-owned archive ingestion module, and `package_archive_cache.spl` APIs. The ingestion API must receive immutable pinned content/handles, not reopen validated paths.

### P0 — No demand graph or lazy import materializer

**Impact:** Highest. Even with archives, the frontend has no symbol/operation request graph, no proxy state machine, and no minimal body closure. This prevents Java-class-style metadata loading and forces broad semantic/HIR work.

**Concrete owner:** Frontend/HIR owner. Primary layers: `src/compiler/10.frontend`, `20.hir`, `30.types`, `35.semantics`; new canonical interfaces `ImportMaterializationV1` and `HirDemandSetV1`.

### P0 — No MIR admission proof for deferred state

**Impact:** Correctness stop gate. Lazy frontend work cannot safely cut over until every requested type, body, initializer, provider, and aspect dependency is concrete and snapshot-bound before MIR.

**Concrete owner:** MIR boundary owner. Primary files: `driver_hir_pipeline_lowering.spl`, `driver_pipeline_lowering.spl`, and a new `MirAdmissionV1` verifier adjacent to `src/compiler/50.mir`.

### P1 — Package schedule is ordering metadata, not an execution service

**Impact:** High. SCC order is computed, but there is no shared coordinator with immutable actions, resource pools, cancellation, memory budgets, single-flight execution, deterministic diagnostics, or dynamic-edge persistence.

**Concrete owner:** Compiler cache/scheduler owner. Primary modules: `package_scc_scheduler.spl`, action index/CAS/tier router, plus a new reusable artifact-service library used by compiler, test, MCP/LSP, and optimizer profiles.

### P1 — Clean artifacts are path-based and not immutably pinned

**Impact:** High correctness and cache-hit risk. Verification followed by later reopen leaves a TOCTOU window; SCC publication does not yet provide a single atomic visibility boundary for all members.

**Concrete owner:** CAS/archive owner. Primary file: `package_archive_cache.spl`; required additions are immutable content handles or digest-addressed reads and transactional SCC batch commit.

### P1 — Backend tiers are disconnected

**Impact:** High for latency. LLVM and Cranelift selection exists, and interpreter hotspot tiering exists, but package action identity does not return cached bytecode/Cranelift synchronously or enqueue compatible LLVM promotion in the background.

**Concrete owner:** Backend/tiering integration owner. Primary modules: `driver_aot_native_output.spl`, `src/compiler/95.interp/execution`, cache promotion APIs, and the new artifact-service queue.

### P2 — Generic shape sharing is absent

**Impact:** Medium-to-high on generic-heavy builds. Current specialization can duplicate semantic, MIR, optimization, and object work because no canonical layout-shape/dictionary implementation key is present.

**Concrete owner:** Type/MIR specialization owner. Primary layers: `30.types`, `50.mir`, monomorphization/specialization code, package metadata keys.

### P2 — Common asynchronous file-view abstraction is absent

**Impact:** Medium and additive. It can reduce blocking and excess reads, but it does not replace the larger wins from archive reuse and demand closure. The named design interfaces do not exist in production.

**Concrete owner:** Standard-library file-I/O owner with compiler parser/SMF consumers. Implement `FileReadPolicyV1` and `ReadOnlyFileViewV1`, then route archive and parser reads through it.

### P3 — Evidence is insufficient

**Impact:** Prevents optimization claims. Current phase logging does not prove opened source count, mapped/read bytes by section, action hits/misses, materialization count, SCC concurrency, backend queue delay, or foreground interference.

**Concrete owner:** Performance evidence owner. Add counters at admission, package route, archive reader, demand materializer, HIR/MIR admission, and backend publication boundaries.

## Recommended implementation order

1. Freeze immutable archive-reader and demand/MIR-admission interfaces.
2. Add compiler-owned archive ingestion with transactional SCC visibility and pinned content.
3. Add metadata proxies, single-flight materialization, `HirDemandSetV1`, and fail-closed `MirAdmissionV1`.
4. Replace schedule environment handoff with a reusable action-service coordinator and typed action graph.
5. Connect cached bytecode/Cranelift foreground results and snapshot-compatible asynchronous LLVM promotion.
6. Add layout-shape generic reuse.
7. Add common asynchronous file views and parser acceleration.
8. Run matched cold/warm Go/Simple fixtures and prove warm zero-source-open behavior before removing compatibility paths.

## Conclusion

The repository now has a credible immutable snapshot, persistent package index, SCC ordering, typed package metadata, and archive-validation foundation. The demand-driven pipeline itself is not yet implemented end-to-end. The decisive missing bridge is from verified archive sections to lazy frontend facts and then to a formally closed MIR set. Until that bridge and its action-service execution path exist, current cache/index work reduces discovery and invalidation cost but cannot deliver the planned Go/Java-like warm compilation behavior.
