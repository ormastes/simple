# Feature: Parser Framework

## Raw Request
`$dev with agents teams impl parser_framework_plan.md`

Authoritative plan: `doc/03_plan/platform/structural_compute/parser_framework_plan.md`.

## Task Type
feature

## Refined Goal
Implement the generic multi-dialect parser framework and canonical Simple dialect across representation repair, deterministic CPU parsing, SIMD indexes, GPU lexical execution, and incremental parsing, with parity and measured dispatch evidence for every supported mode.

## Acceptance Criteria
- AC-1: The canonical parser path stores source contiguously, represents tokens by source spans with interned values, stores syntax in index-based SoA arenas, and releases stage-bounded arenas; focused memory evidence proves it does not allocate per-character objects, copy token strings, or retain completed-stage arenas.
- AC-2: Public `ParseDialect`, `ParseRuntime`, `ParseRequest`, `ParseResult`, `ParseActionSink`, policy, receipt, tag, and mapping contracts exist under the plan-owned paths, and the Simple dialect adapter uses them without changing existing parser byte, token, syntax, or diagnostic behavior.
- AC-3: Repeated CPU parses of the same request produce stable ordered tokens, syntax arenas, tags, mappings, diagnostics, stage receipts, and identical `deterministic_hash` values.
- AC-4: The SIMD structural-index path validates UTF input and classifies delimiters, quotes, newlines, and indentation; the scalar grammar consumes those indexes and produces the same ordered result and deterministic hash as scalar CPU parsing.
- AC-5: The GPU lexical path implements chunk summaries, scan composition, count/scan/emit token production, and region parsing for top-level declarations and function bodies without using the forbidden object-heavy token/AST representation; it produces the same ordered result and deterministic hash as CPU parsing.
- AC-6: Incremental parsing derives lexical stabilization and changed-region boundaries from an edit, reuses unchanged arena regions, emits old-to-new mapping edges plus invalidation, and produces the same result and deterministic hash as a full reparse of the edited snapshot.
- AC-7: With `TagDemand` disabled, executable allocation evidence reports zero tag/index allocation.
- AC-8: A retained benchmark records CPU/SIMD/GPU crossover measurements per parser stage on realistic fixtures, and `auto` dispatch uses those recorded thresholds while preserving parity.
- AC-9: Modern SSpec scenarios execute the primary scalar, SIMD, GPU, incremental, tag-demand, and auto-dispatch flows with direct value assertions and mirrored operator-readable Markdown under `doc/06_spec`; no executable `_spec.spl` exists under `doc/06_spec`.
- AC-10: Unit/integration coverage exercises malformed UTF, delimiter/quote/indent continuation, chunk boundaries, diagnostics, region boundaries, arena reuse/invalidation, deterministic ordering, and policy rejection, and all focused parser/compiler checks pass once.
- AC-11: Research, selected feature/NFR requirements, architecture, system-test plan, detail design, agent-task ownership, implementation, generated manual, and parser guide artifacts are current and mutually traceable; no pending requirement-option document remains.
- AC-12: Final high-capability review verifies the cooperative merge, generated-manual quality, owned-path scope, direct-runtime/env guards, and every AC against authoritative current-state evidence before the lane can report `STATUS: PASS`.

## Scope Exclusions
- Clang C/C++ parsing remains in the `clang_bridge` lane.
- HTML tree-builder semantics remain in the `html_css_parser` lane.
- Dialects other than the Simple dialect remain consumer-owned.
- GPU execution over the current object-heavy token/AST representation is forbidden.
- Resident-GPU arena placement remains dependent on the separate `gpu_mmu` lane; hybrid SIMD work does not wait for it.

## Cooperative Review
- Sidecar lanes: representation/contracts; CPU Simple-dialect parity; SIMD structural indexes; GPU lexical/region path; incremental parse; independent tests/manual/benchmark audit.
- Shared interfaces frozen before fan-out: `ParseDialect`, `ParseRuntime`, `ParseRequest`, `ParseResult`, `ParseActionSink`, `ParseActionProgram`, `TagSchema`, `MappingPolicy`, `IncrementalPolicy`, `StageReceipt`, `StructuralIndex`, and index-based syntax arena identifiers.
- Manual primary steps: `Build the canonical parser representation`; `Parse the Simple dialect on the scalar CPU`; `Reuse SIMD structural indexes`; `Compose GPU lexical chunks in source order`; `Reparse only stabilized changed regions`; `Select the measured execution mode`; `Compare deterministic parser results`.
- Shared setup/checker helpers: `parser_framework_fixture`, `parse_result_fingerprint`, `expect_parse_results_equal`, `expect_stage_receipts_deterministic`, `expect_tag_demand_allocation`, and `expect_incremental_matches_full`.
- Temporary implementations must fail explicitly with `assert(false)` or `fail(...)`; placeholder passes and hard-coded success results are forbidden.
- Merge owner and final reviewer: root Codex, normal/highest-capability review after all sidecar lanes; independent tests/manual sidecar owns the first generated-manual audit, root owns final acceptance.

## Research Summary
### Existing Code
- The canonical driver reaches the SoA parser through `driver_source_pipeline_parsing.spl:254-265`, `frontend.spl:69-96`, and `_FlatAstBridge/module_assembly.spl:698-729`.
- Existing SoA AST pools and reset logic are reusable; current lexer source/token storage still copies strings and character arrays.
- Frozen structural contracts and all optimized/incremental executors are absent; current incremental state is file-level invalidation only.
- Prior memory evidence and focused single/multifile wrappers provide the Wave-0 baseline; current parser tests provide scalar behavior oracles but not framework parity.

### Reusable Modules
- Compiler SoA AST pools, flat-to-rich bridge ordering, stable hash utilities, `SourceFile.content`, `GenArena<T>`, `simd_scan`, and evidence-receipt validation.

### Domain Notes
- Span tokens require snapshot lifetime; observable hashes cannot contain interner/arena IDs.
- SIMD structural indexing must retain boundary state and remain semantics-free.
- GPU lexing is bounded finite-state scan plus integer count/scan/emit; nested grammar retains scalar/region fallback.
- Incremental reuse is valid only when lexical and grammar context remain compatible and the result equals a clean full reparse.

### Open Questions
- NONE — user selected F2 + N2 on 2026-07-31.

<!-- sdn-diagram:parser-framework-dependencies -->
```sdn
parser_framework = {
  source: canonical_snapshot
  scalar: {tokens, syntax, diagnostics, receipt}
  optimized: [simd_index, gpu_lex_region, incremental_reuse]
  invariant: deterministic_result_parity
  consumers: [simple_dialect, css_dialect, html_dialect, constrained_c]
}
```

## Requirements
- REQ-1 (AC-1): Canonical snapshot, byte spans, interned token values, indexed arenas, and bounded lifetime — area: compiler frontend + structural parse.
- REQ-2 (AC-2/3): Frozen public contracts, Simple adapter, ordered deterministic result parity — area: structural parse + structural adapter.
- REQ-3 (AC-4): Stateful SIMD UTF/structural indexes consumed by scalar grammar — area: structural parse runtime.
- REQ-4 (AC-5): Associative bounded GPU summaries and ordered count/scan/emit with explicit fallback — area: structural parse runtime.
- REQ-5 (AC-6): Edit stabilization, region reuse, mappings, invalidation, and full-reparse equality — area: structural parse runtime.
- REQ-6 (AC-7/8): Zero-demand allocation evidence and retained crossover benchmarks driving `auto` — area: tests/perf.
- REQ-7 (AC-9/10): Modern SSpec manual plus focused unit/integration boundary and parity coverage — area: test/doc.
- REQ-8 (AC-11/12): Traceable artifacts, cooperative review, guards, and authoritative final verification — area: plan/doc/verify.

## Architecture

### Module Plan
| Module | Path | Role |
|---|---|---|
| identity/model | `src/lib/common/structural/{identity,parse/{contracts,model,dialect,output_plan}}.spl` | immutable spans, segmented arenas, programs, result |
| sink/runtime | `src/lib/nogc_async_mut/structural/parse/{action_sink,runtime}.spl` | indexed ordered emission and dispatch |
| executors | `src/lib/nogc_async_mut/structural/parse/{scalar,structural_index,parallel_lex,incremental,auto_profile}.spl` | scalar/SIMD/GPU/incremental/auto modes |
| Simple adapter | `src/compiler/10.frontend/{canonical_ast,structural_adapter}/` | Simple schema/program and legacy bridge |

### Dependency Map
- `identity -> model -> dialect/action_sink/executors -> runtime`; compiler adapter depends downward on common; GC GPU adapter depends on common plan plus existing GPU owner.
- No circular dependencies: common never imports compiler, executors do not select each other, and the legacy bridge is one-way.

### Decisions
- D-1: `ParseDialect` is a declarative validated data class, not a factory/one-implementation trait.
- D-2: Snapshot-owned bytes, byte-span tokens, immutable relative-span SoA segments, scoped identities, and semantic hashes form the canonical representation.
- D-3: Exact count/scan/emit through one sink provides deterministic scalar/SIMD/GPU output; atomic append is forbidden.
- D-4: Incremental segment reuse requires source plus lexical/grammar/parent context fingerprints.
- D-5: `auto` fails back to scalar unless matching retained evidence proves parity and N2's 1.5x threshold.

### Public API
- `parse_runtime(dialect: ParseDialect) -> Result<ParseRuntime, text>` validates one runtime instance.
- `parse_request(runtime: ParseRuntime, request: ParseRequest) -> Result<ParseResult, text>` is the sole execution entry.
- `parse_result_fingerprint` and `parse_results_equal` define parity independent of allocation IDs.
- `build_structural_index`, `compose_chunk_summaries`, `emit_parallel_tokens`, `incremental_parse_plan`, and `select_parse_mode` are the frozen executor seams.

<!-- sdn-diagram:parser-framework-architecture -->
```sdn
SourceSnapshot -> ParseRequest -> ParseRuntime -> ParseActionSink -> ParseResult
ParseDialect -> ParseRuntime
ParseRuntime -> [Scalar, SimdIndex, GpuLexRegion, Incremental]
```

### Requirement Coverage
- REQ-1/2/3 -> identity, model, dialect, sink, scalar, Simple adapter.
- REQ-4/5/6 -> structural index, parallel/GPU, incremental executors.
- REQ-7 -> sink demand gate and auto profile.
- REQ-8 -> specs/manual/agent plan and final review.

## Phase
arch-done

## Phase
research-done

## Log
- dev: Created state file with 12 acceptance criteria (type: feature); froze shared interface and manual-step vocabulary before agent fan-out.
- research: Five agent lanes plus root incremental research identified reusable compiler/library owners, domain constraints, eight requirement groups, and three feature/NFR bundles; awaiting mandatory user selection.
- requirements: User selected F2 complete phased framework and N2 balanced targets; final requirement docs written and option docs deleted.
- arch: Froze 15-module acyclic design, declarative data contracts, ordered sink, executor seams, and Simple compatibility boundary.
- design-review: Corrected default-tier ownership, completed public type definitions, added indexed output writes and private fallback, separated semantic parity from telemetry, and made segment reuse/snapshot lineage representable.
