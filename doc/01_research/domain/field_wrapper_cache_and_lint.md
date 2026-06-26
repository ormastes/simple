<!-- codex-research -->

# Field Wrapper Cache And Lint Research

Agent C read-only verification/research note, 2026-06-07.
Updated after integration verification, 2026-06-07.

## Similar-Name Lint Algorithm

Primary sources checked:

- Levenshtein, "Binary Codes Capable of Correcting Deletions, Insertions and Reversals" (1966): https://bibbase.org/network/publication/levenshtein-binarycodescapableofcorrectingdeletionsinsertionsandreversals-1966
- Damerau, "A technique for computer detection and correction of spelling errors" (CACM, 1964), DOI 10.1145/363958.363994: https://cir.nii.ac.jp/crid/1361137045892695424?lang=en
- Myers, "A fast bit-vector algorithm for approximate string matching based on dynamic programming" (Information Processing Letters, 1999): https://www.sciencedirect.com/science/article/pii/S0020019099001210
- Burkhard and Keller, "Some Approaches to Best-Match File Searching" (CACM, 1973), DOI 10.1145/362003.362025: https://www.researchgate.net/publication/234803118_Some_Approaches_to_Best-Match_File_Searching

Recommendation: keep the lint local to each child method and its inherited parent-method set. Use bounded Damerau-Levenshtein / optimal-string-alignment distance with early exit, not a BK-tree, for the first implementation. Parent method sets are small enough that O(child_methods * inherited_methods * name_length * threshold-band) is simpler and faster in practice than maintaining an index. Damerau-style transposition support directly targets common identifier typos such as `render_farme` vs `render_frame`.

Suggested thresholds:

- Ignore names shorter than 4 characters.
- Warn at distance <= 1 for max length 4..8.
- Warn at distance <= 2 for max length >= 9.
- Never warn for exact overrides.
- Suppress with `@name_checked`.
- Skip expected accessor-prefix siblings such as `get_x` vs `set_x` / `is_x`.

The current Rust lint implementation already follows this shape in `src/compiler_rust/compiler/src/lint/checker_names.rs`: inherited method scan, `@name_checked` suppression, expected accessor-prefix skip, threshold 1 or 2, and bounded Damerau-Levenshtein with row-min early exit.

## Formal Verification And Cache Findings

Current formal verification cache surfaces:

- `src/compiler_rust/lib/std/src/verification/fingerprint.spl` has semantic/public ABI fields and helpers: `semantic_hashes`, `compute_with_semantics`, `from_hashes_with_semantics`, `semantic_fingerprint`, `public_abi_fingerprint`, `accessor_fingerprint`, `field_wrapper_fingerprint`, and `dependency_semantic_fingerprint`.
- `src/compiler_rust/lib/std/src/verification/cache.spl` has transitive `invalidate_dependents`.
- `src/compiler_rust/compiler/src/incremental.rs` has Rust seed semantic exports/dependencies and `invalidate_semantic_export`.
- `src/compiler_rust/compiler/src/incremental_builder.rs` extracts simple type, field, and `get_` / `set_` / `is_` accessor semantic exports and includes `test_semantic_field_wrapper_change_invalidates_cached_dependent`.
- Loader-side Pure Simple has semantic fingerprint cache records in `src/compiler/99.loader/loader/module_loader.spl` and SMF note reads in `src/compiler/99.loader/loader/smf_cache.spl`.

Initial live verification command:

```sh
SIMPLE_LIB=src bin/simple test test/00_formal_verification/compiler/cache_correctness_spec.spl --mode=interpreter --clean --json
```

Initial result: FAIL, `total_passed=10`, `total_failed=11`.

Exact observed causes:

- 9 cache-store scenarios fail because `VerificationCache.store` calls `current_timestamp`, which imports `host.time`; live interpreter reports `variable time not found`. The available std path appears to be `core.time.now_iso8601`.
- 2 fingerprint/hash scenarios fail because `simple_hash` collides on tested inputs:
  - `simple_hash("hello") == simple_hash("world")`
  - `Fingerprint.from_hashes("src_a", "lean", [], "v4.x")` matches `Fingerprint.from_hashes("src_b", "lean", [], "v4.x")`

Resolved integration result:

- `VerificationCache.store` no longer depends on the missing `host.time` import in this path.
- `simple_hash` was replaced with deterministic escaped content fingerprints, so the formal cache no longer collapses different semantic inputs.
- `SIMPLE_LIB=src bin/simple test/00_formal_verification/compiler/cache_correctness_spec.spl` now reports 22 examples, 0 failures.
- `SIMPLE_LIB=src bin/simple test/01_unit/compiler/loader/module_loader_semantic_cache_spec.spl --mode=interpreter --clean` reports 2 passed, 0 failed.
- Rust seed check: `CARGO_INCREMENTAL=0 CARGO_TARGET_DIR=/tmp/simple-rust-seed-target cargo test -p simple-compiler test_semantic_field_wrapper_change_invalidates_cached_dependent --manifest-path src/compiler_rust/Cargo.toml` reports 1 passed, 0 failed.

Conclusion: the implemented Pure Simple proof-cache and loader evidence now proves the field-wrapper semantic invalidation shape for the covered cache model: stale verified entries are not returned when public ABI, accessor, or field-wrapper dependency fingerprints change, and transitive/cyclic dependents are invalidated.
