<!-- codex-architecture -->
# Parser Framework Architecture

**Status:** Accepted for F2 + N2 implementation
**Parent:** `doc/04_architecture/compiler/mdsoc/mdsoc_plus_tagged_structural_compute_architecture.md` Part II
**Requirements:** `doc/02_requirements/feature/parser_framework.md`, `doc/02_requirements/nfr/parser_framework.md`

## Decision

The parser framework is a structural virtual capsule with immutable cross-tier contracts in `common`, default mutable execution in `nogc_async_mut`, one snapshot/span representation, one ordered `ParseActionSink`, and one `ParseResult`. Scalar, SIMD, GPU, incremental, and auto executors are replaceable execution transforms below that contract. The Simple frontend owns only its schema/program bundle and compatibility bridge.

<!-- sdn-diagram:id=parser_framework.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=parser_framework.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

SourceSnapshot -> ParseRequest
ParseDialect -> ParseRuntime
ParseRequest -> ParseRuntime
ParseRuntime -> ScalarExecutor
ParseRuntime -> StructuralIndexExecutor
ParseRuntime -> ParallelLexExecutor
ParseRuntime -> IncrementalExecutor
ScalarExecutor -> ParseActionSink
StructuralIndexExecutor -> ScalarExecutor
ParallelLexExecutor -> ParseActionSink
IncrementalExecutor -> ParseActionSink
ParseActionSink -> ParseResult
SimpleDialectAdapter -> ParseDialect
ParseResult -> LegacyFrontendBridge
BenchmarkEvidence -> AutoThresholds
AutoThresholds -> ParseRuntime
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=parser_framework.arch hash=sha256:auto
SourceSnapshot -> ParseRequest -----> ParseRuntime <----- ParseDialect <----- SimpleDialectAdapter
                                         |   |   |   |
                                         v   v   v   v
                                      scalar SIMD GPU incremental
                                         \   |   |   /
                                          ParseActionSink
                                                |
                                                v
                                           ParseResult -> LegacyFrontendBridge
BenchmarkEvidence -> AutoThresholds ------------^
```

</details>
<!-- sdn-diagram:end -->

## Modules

| Module | Path | Responsibility |
|---|---|---|
| Structural identity | `src/lib/common/structural/identity.spl` | `EntityRef`, `SnapshotId`, `SourceSpan`; imports existing `ArtifactId` |
| Parse contracts/model | `src/lib/common/structural/parse/{contracts,model,dialect,output_plan}.spl` | Immutable request/result/program records, snapshot bytes, segmented SoA arenas, output plans |
| Ordered sink/runtime | `src/lib/nogc_async_mut/structural/parse/{action_sink,runtime}.spl` | Mutable exact reservation/emission, validation, selection, fallback, hashing |
| Executors | `src/lib/nogc_async_mut/structural/parse/{scalar,structural_index,parallel_lex,incremental,auto_profile}.spl` | Scalar oracle, SIMD indexes, GPU-facade plan, reuse, measured auto |
| Public surface | `src/lib/nogc_async_mut/structural/parse/__init__.spl` | Explicit common-contract and default-runtime exports |
| Simple schema | `src/compiler/10.frontend/canonical_ast/simple_schema.spl` | Simple token/node/action kind IDs and SoA payload columns |
| Simple dialect | `src/compiler/10.frontend/structural_adapter/simple_dialect.spl` | Builds the declarative Simple `ParseDialect` |
| Legacy bridge | `src/compiler/10.frontend/structural_adapter/legacy_bridge.spl` | Temporary parity conversion to current `ParserModule`; no grammar fork |

## Current in-tree status

- `src/lib/common/structural/parse/parse_types.spl` and `src/lib/common/structural/parse/parse_cpu_reference.spl` implement the current wave-1 CPU-reference foundation (schema, request/result types, action sink, and scalar oracle).
- `src/lib/nogc_async_mut/structural/parse` executors and additional common modules (`contracts`, `model`, `dialect`, `output_plan`) are still documented as planned work in the architecture; they are not yet present in this worktree.
- `doc/03_plan/platform/structural_compute/parser_framework_plan.md` owns the merge order for the planned follow-up waves.

## Dependency rules

- `common.structural.identity` depends only on the existing content-addressed `ArtifactId`; parse model depends on identity and bytes/crypto helpers.
- Dialect, sink, and executors depend on the parse model; runtime alone selects executors. Executors never import one another except scalar consuming a structural index.
- The compiler adapter depends downward on common parse contracts. Common code never imports compiler frontend types.
- Default-tier GPU execution composes through existing `nogc_async_mut` GPU/MMU/placement owners; common parse code contains no `rt_*` imports and no backend fields. No GC-only parser adapter or root `variants/` mode exists.
- The legacy bridge is the only module allowed to construct current rich frontend objects. No reverse dependency enters canonical arenas.
- No circular dependencies: verified by construction; `model -> dialect/sink/executors -> runtime` is one-way.

## Architecture decisions

- **ADR-PARSE-1 — Declarative dialect bundle.** `ParseDialect` is a validated data class, not a trait/factory. The initial Simple dialect and future consumer dialects supply program tables; executors stay generic and GPU-serializable.
- **ADR-PARSE-2 — Snapshot-owned bytes.** Source is `[u8]` plus newline starts; tokens hold half-open byte spans and optional string-table IDs. Line/column is derived, never token identity.
- **ADR-PARSE-3 — Owned immutable segments, one canonical result.** Common parse arenas contain immutable typed SoA segments with relative spans and scoped identities. The legacy object tree is an output bridge during cutover, not retained storage or a second grammar.
- **ADR-PARSE-4 — Ordered two-pass emission.** Executors count, exclusive-scan exact integer offsets, then emit into disjoint source-ordered ranges. Atomic append and scheduler-order commit are invalid.
- **ADR-PARSE-5 — Optimization below parity gate.** SIMD emits only structural indexes. GPU handles bounded lexical state plus eligible regions. Unsupported cases return an observable fallback reason before output mutation.
- **ADR-PARSE-6 — Segment-granular incrementality.** Immutable arena segments carry region and complete continuation-state fingerprints. Reuse requires matching region bytes, entry/exit lexical state, grammar rule, parent region, schema, and generation; otherwise the region reparses.
- **ADR-PARSE-7 — Evidence-driven auto.** Thresholds are versioned by dialect/schema/backend/host/fixture family. Missing, stale, or sub-1.5× evidence selects scalar; no environment read occurs in the hot path.

## MDSOC evaluation

The stable model/dialect/runtime forms a virtual capsule shared across compiler and consumer dialects. SIMD, GPU, incremental, tags, mappings, diagnostics, and measurement are feature transforms that write through the same sink/result contract. Runtime composition is limited to explicit executor selection; grammar remains single-source in the Simple dialect program.

## Startup, hot path, caches, invalidation

Dialect validation and retained-threshold loading occur once per runtime instance. Parse requests do no filesystem scans, subprocesses, or environment reads. Snapshot string tables, structural indexes, and arena segments are request/revision owned. An edit invalidates only overlapping lexical chunks, context-dependent successor chunks through stabilization, changed regions, mappings, and downstream dependency keys. Threshold evidence invalidates on dialect/schema/runtime/backend/host identity mismatch.

## Failure contract

Invalid spans, malformed UTF, canonical count overflow, stale snapshot/segment identity, invalid program tables, unsupported GPU state cardinality, unavailable placement, or stale thresholds return typed errors/diagnostics/fallback receipts. Optimized execution uses private staging; partial output is discarded before scalar fallback. `FallbackPolicy.RequireRequested` returns an error instead of falling back.
