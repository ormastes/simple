<!-- codex-research -->
# Parser Framework — Local Research

**Date:** 2026-07-31
**Scope:** `doc/03_plan/platform/structural_compute/parser_framework_plan.md`

## Current canonical flow

`SourceFile.content` is passed through the driver to `parse_full_frontend`, then `parse_and_build_module_scoped`; the flat-AST bridge resets pools, runs `parse_module_body`, and converts the flat result into the object-heavy `ParserModule` (`src/compiler/80.driver/driver_source_pipeline_parsing.spl:254-265`, `src/compiler/10.frontend/frontend.spl:69-96`, `src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl:698-729`). A sibling core entry is `core_frontend_parse` → `parse_module`/`parse_module_file` (`src/compiler/10.frontend/core/frontend.spl:10-43`, `src/compiler/10.frontend/core/parser.spl:838-886`).

## Reusable implementation

- The compiler already owns contiguous `SourceFile.content` (`src/compiler/00.common/driver_source_file.spl:48-75`) and index-based SoA AST pools (`src/compiler/10.frontend/core/_AstExpr/nodes.spl:85-99`, `src/compiler/10.frontend/core/ast_stmt.spl:38-47`, `src/compiler/10.frontend/core/_Ast/decl_nodes.spl:224-293`). `ast_reset` clears and reuses the pools (`src/compiler/10.frontend/core/_Ast/module_state.spl:440-623`).
- Source-order declaration traversal and `function_order` provide ordered-commit precedents (`src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl:117-180,633-677`). Stable hashing precedents are SHA-256 symbol serialization and FNV-1a (`src/compiler/35.semantics/symbol_id/stable_id.spl:46-64`, `src/compiler/70.backend/linker/lib_smf.spl:400-416`).
- The library parser offers adapter-sized entry points: `lex_source`, `parse`, `parse_expr`, and `parse_stmt` (`src/lib/common/parser/lexer.spl:8-27`, `src/lib/common/parser/parser.spl:437-459`).
- Reusable storage/compute patterns include `GenArena<T>` (`src/lib/nogc_sync_mut/mem/gen_arena.spl:1-140`), flat positional postings (`src/lib/common/search/inverted_index.spl:58-143`), byte-scan oracle/dispatch (`src/lib/common/search/simd_scan.spl:38-162`), and fail-closed evidence receipt validation (`src/lib/nogc_sync_mut/spec/evidence_receipt.spl:26-124`).
- SCV has content-addressed immutable syntax nodes and full-reparse hash reuse (`src/lib/scv/parser.spl:124-129`, `src/lib/scv/parser_registry.spl:75-115`, `src/lib/scv/parser_incremental.spl:1-51`), useful as an oracle but not as the required region-incremental implementation.

## Representation defects and missing contracts

- The compiler lexer duplicates source into multiple buffers and `source.chars()` (`src/compiler/10.frontend/core/lexer.spl:61-73,219-233`; `lexer_struct.spl:135-181`). Tokens own copied text and use character offsets even though canonical diagnostics require byte spans (`lexer_types.spl:34-48`, `src/compiler/00.common/diagnostics/span.spl:6-20`). The library lexer likewise embeds text/line/column and slices source repeatedly (`src/lib/common/parser/lexer.spl:8-24,35-41,83-192`).
- `src/lib/common/structural/parse/`, `src/compiler/10.frontend/canonical_ast/`, and `src/compiler/10.frontend/structural_adapter/` do not exist. Neither compiler nor library defines the frozen parser contracts, tags/mappings/index shards, ordered result receipt, or deterministic parse hash.
- Parser diagnostics are currently printed flags; `parser_get_errors` and its count return hard-coded empty results (`src/compiler/10.frontend/core/parser.spl:253-278,888-898`).
- Existing incremental state is file-hash dependency invalidation, while lexer snapshots are speculative backtracking. Neither provides edit stabilization, unchanged-region arena reuse, old→new mappings, or full-reparse equality (`src/compiler/80.driver/incremental.spl:14-117`, `src/compiler/10.frontend/core/lexer.spl:642-711`).
- SIMD scan reports scalar-only; no structural bitmap classifier exists (`src/lib/common/search/simd_scan.spl:31-104`). The GPU memory wrapper is CUDA-only/incomplete and must not become the parser foundation (`src/lib/gc_async_mut/gpu/memory.spl:63-113,179-185`).

## Existing evidence and risks

The prior memory survey records a 64 GB/1777-file failure and calls for spans, interning, SoA, and bounded lifetimes (`doc/01_research/compiler/parser/ast_memory_management_survey_2026-07-24.md:1-18,33-141`). Existing single/multifile memory wrappers are reusable, but the tracked bug still reports unreclaimed/reset hazards (`scripts/check/check-stage4-selfhost-parse-memory.shs`, `scripts/check/check-stage4-selfhost-parse-memory-multifile.shs`, `doc/08_tracking/bug/bootstrap_stage4_selfhost_parse_memory_blowup_2026-07-20.md:843-881,1014-1097`). Current parser behavior tests are usable parity baselines; several purported incremental/perf tests are only outline scanners or contain placeholder assertions and are not acceptance evidence.

Dirty parser-adjacent files belong to other lanes, notably `src/compiler/10.frontend/core/_Ast/module_state.spl` and new unit-generic parser specs. This lane must avoid them until ownership is coordinated.

## Conclusion

Reuse the existing SoA AST pools, ordered bridge traversal, source container, hash utilities, and focused memory wrappers. Add the smallest missing owner contracts and span-token representation; do not create a second AST framework or build GPU execution on the current copied-token/object tree.
