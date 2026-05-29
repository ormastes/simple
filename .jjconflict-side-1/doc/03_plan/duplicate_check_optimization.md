# Duplicate-Check Tool — Optimization & Refactoring

## Status: DONE (perf + refactoring + cosine mode perf)

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

### Phase 3: Cosine/Token Mode Performance (DONE)
Implemented the bounded interpreter-safe path instead of a native extern tokenizer:
- Fixed repeated-hash prefilter accounting so repeated lexical windows are found.
- Materialized snippets when duplicate blocks are created, so low-signal filtering and exact grouping use real code instead of empty placeholders.
- Kept token mode on the repeated-hash prefilter path.
- Let cosine mode scan candidate windows across input files so renamed fuzzy duplicates are still considered on bounded inputs.
- Added a cosine-only interpreter guard that samples small files before tokenization on large scopes; token mode still uses the full repeated-hash prefilter.
- Preserved the existing cosine safety limits: block sampling, per-block comparison cap, total comparison cap, cached token reuse, and line-indexed feature extraction.

Validation:
- `bin/simple test test/unit/app/duplicate_check/duplicate_check_spec.spl --mode=interpreter`
- `bin/simple test test/unit/app/duplicate_check/phase1_integration_spec.spl --mode=interpreter`
- `bin/simple test test/system/duplicate_check/duplicate_check_regression_system_spec.spl --mode=interpreter`
- `timeout 60s bin/simple run src/compiler/90.tools/duplicate_check/main.spl duplicate-check src/compiler/90.tools --mode cosine --min-lines 5 --min-tokens 30 --quiet` completed in 34.23s, max RSS 63896KB; exit 1 because one duplicate group was found.

### Remaining Semantic Duplicates (LOW PRIORITY)
14 COPY-PASTE matches remain — all are intentional or impractical to extract:
- 7 platform-specific encoders (AVX2/NEON/RISC-V)
- 3 `stats_summary` (same name, different logic)
- 3 `main` boilerplate (test entry points)
- 1 `get_errors` (would need trait/mixin, Simple lacks inheritance)

### Tooling Follow-Up: Generic Migration False Positives
- The duplicate-check smoke path still prints deprecated-generic warnings for valid index and slice expressions such as `bytes[i]`, `pattern[a:b]`, and `json[j:j+1]`.
- `bin/simple migrate --fix-generics` is not safe for these files today: it rewrites valid list return/variable types such as `[DocEntry]` into `<DocEntry>`, which fails parsing.
- Keep the current syntax until the parser/migrator can distinguish list types, generic type parameters, indexing, and slicing.
