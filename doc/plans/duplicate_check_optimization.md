# Duplicate-Check Tool — Optimization & Refactoring

## Status: DONE (perf + refactoring), REMAINING (cosine mode perf)

## Completed

### Phase 1: Semantic Mode Performance (DONE — pushed)
- **Batch doc extraction**: `find | xargs awk` replaces 1154 individual `file_read()` calls
- **Directory-grouped comparison**: O(sum of group²) instead of O(n²) for 9.5K items
- **Min-hash pre-filter**: `feature_signature()` + `signatures_share_token()` skip ~70% of pairs
- **`_tokenize_doc` O(n²) fix**: cache `bytes()`, range-based word extraction
- **Result**: src/compiler/ semantic scan: >5 min → 62s

### Phase 2: Refactoring Found Duplicates (DONE — pushed)
Extracted 6 shared modules from COPY-PASTE duplicates:

| Module | Location | Consumers |
|--------|----------|-----------|
| `lint_string_utils.spl` | 35.semantics/lint/ | 3 security lint files |
| `header_utils.spl` | 90.tools/header_gen/ | c_header, cpp_header |
| `call_edge_utils.spl` | 10.frontend/core/ | alloc_inference, call_graph |
| `type_utils.spl` | 30.types/type_system/ | bidirectional, expr_infer_calls |
| `SpecializationKey` dedupe | 40.mono/monomorphize/ | engine imports from types |
| `sanitize_c_name` | 90.tools/header_gen/ | added to header_utils |

Net: +203 lines shared, -289 lines removed. Semantic matches: 70 → 62.

### Coupling/Cohesion Audit (DONE)
All shared modules: CBO 0-1, no cycles, no layer violations, high cohesion.

## Remaining Work

### Cosine/Token Mode Performance (NOT STARTED)
Cosine mode took 148 min on `90.tools/` alone — impractical in interpreter.
Root cause: byte-by-byte tokenization of entire file contents in interpreter is ~100x slower than native.

**Options (pick one):**
1. **Native extern tokenizer** — add `rt_tokenize_file(path) -> [Token]` Rust extern. Fastest, but requires bootstrap rebuild.
2. **Shell-based tokenizer** — like batch doc extraction, use `awk` to pre-tokenize files. Medium effort, no bootstrap.
3. **Skip cosine in interpreter** — only support cosine mode when running compiled binary. Cheapest.

### Remaining Semantic Duplicates (LOW PRIORITY)
14 COPY-PASTE matches remain — all are intentional or impractical to extract:
- 7 platform-specific encoders (AVX2/NEON/RISC-V)
- 3 `stats_summary` (same name, different logic)
- 3 `main` boilerplate (test entry points)
- 1 `get_errors` (would need trait/mixin, Simple lacks inheritance)
