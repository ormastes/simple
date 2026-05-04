# Duplicate Check Semantic Follow-Up Plan

## Context

The duplicate-check refactor is functionally restored for the public CLI:

- `simple duplicate-check` exposes stable `semantic`, `token`, and `cosine` modes.
- `token` and `cosine` lexical flows are active and covered by passing unit and system tests.
- semantic mode no longer crashes in the unit/runtime path.

The remaining gap is narrower:

- a small semantic CLI fixture can still complete with:
  - `Source: 0 items, 0 documented`
  - `Summary: 0 total, 0 documented ...`
- this means semantic mode is stable, but at least one end-to-end CLI path is still under-counting extracted documentation items.

## Goal

Make semantic mode produce non-zero extracted items for the current small-fixture CLI scenario, then tighten regression coverage so the system spec requires positive semantic extraction rather than merely a non-crashing semantic run.

## Scope

In scope:

- semantic-mode file collection and filtering
- semantic-mode doc extraction entrypoints
- semantic-mode item aggregation and documented-item filtering
- semantic CLI execution path differences versus direct unit invocation
- regression tests for positive semantic extraction

Out of scope:

- changing the restored `token` or `cosine` public behavior
- expanding semantic matching quality beyond the current documented fixture scenario
- general semantic embedding improvements unrelated to the zero-item CLI path

## Current Known State

Code already fixed:

- `src/compiler/90.tools/duplicate_check/semantic.spl`
  - semantic aggregation no longer drops entries during merge
  - text fallback no longer depends on the broken previous similarity path
- `src/compiler/90.tools/duplicate_check/doc_extractor.spl`
  - top-level `me` methods are no longer misclassified as standalone functions
  - content hashing no longer uses the overflow-prone hash helper
- `src/compiler/90.tools/duplicate_check/embedding_cache.spl`
  - cache updates are explicit instead of relying on mutating a copied struct

Verified today:

- semantic unit spec passes
- duplicate-check regression system spec passes

Remaining behavior:

- the semantic CLI regression fixture still allows a successful run with zero extracted items

## Suspected Root-Cause Areas

1. File collection mismatch
   - semantic CLI run may collect a different file set than the direct extractor/unit path
   - excludes, path normalization, or fixture directory reuse may still suppress intended source files

2. Semantic-path filtering mismatch
   - extracted items may be produced but filtered out before report construction
   - documented vs undocumented partitioning may be correct in unit scope but not in CLI scope

3. Runtime-path input differences
   - the CLI path may read files through a different environment or source-root assumption than the direct spec repro
   - relative path handling may differ between standalone repros and system-spec execution

4. Report-path masking
   - the semantic report may still be built from `empty_report()` or an equivalent no-op branch after successful extraction

## Investigation Plan

### Phase 1: Trace semantic CLI data flow

Instrument and compare these checkpoints for the same fixture:

1. `collect_files(target_path, config)` result
2. per-file `extract_docs_from_file(file)` count
3. `all_entries.len()` before documented filtering
4. `documented.len()` and `missing_docs.len()`
5. final `SemanticReport.total_items` and `items_with_docs`

Comparison runs:

- direct one-off repro invoking `extract_docs_from_file()`
- direct call into `run_semantic_analysis()`
- CLI invocation through `bin/simple duplicate-check`
- system-spec invocation through `rt_process_run(...)`

Expected output from this phase:

- the first checkpoint where counts diverge between direct semantic invocation and CLI execution

### Phase 2: Patch the remaining semantic no-op path

Once divergence is found, patch the smallest correct layer:

- if file collection is wrong: fix path/exclude handling in the semantic entry flow
- if extraction is skipped: fix the call path or file-read fallback
- if aggregation/filtering is wrong: fix the semantic report assembly
- if reporting is masking real counts: fix formatter input selection or early-return branching

Constraints:

- do not relax lexical mode coverage
- do not revert the current stable semantic fallback behavior
- keep JSON/text semantic report fields stable unless a bug requires documented clarification

### Phase 3: Tighten regression coverage

Update regression coverage so the positive semantic case is explicit.

Required assertions to add or restore:

1. semantic CLI fixture produces `Source:` with a non-zero item count
2. semantic CLI fixture produces a non-zero documented count
3. semantic fallback still occurs when Ollama is unavailable
4. semantic unit/integration coverage proves the same fixture yields extracted doc items through the real semantic entrypoint

## Files Expected To Change

Primary code:

- `src/compiler/90.tools/duplicate_check/semantic.spl`
- `src/compiler/90.tools/duplicate_check/doc_extractor.spl`
- `src/compiler/90.tools/duplicate_check/main.spl`
- `src/compiler/90.tools/duplicate_check/formatter.spl`

Possible supporting code:

- `src/compiler/90.tools/duplicate_check/detector_files.spl`
- `src/compiler/90.tools/duplicate_check/cache.spl`

Tests/docs:

- `test/system/duplicate_check/duplicate_check_regression_system_spec.spl`
- `test/unit/app/duplicate_check/semantic_spec.spl`
- `doc/07_guide/tooling/duplicate_check.md`

## Verification Plan

Minimum required:

1. `bin/simple test test/unit/app/duplicate_check/semantic_spec.spl`
2. `bin/simple test test/system/duplicate_check/duplicate_check_regression_system_spec.spl`
3. direct CLI semantic run on the small fixture showing non-zero extracted items

Recommended bundle:

1. `bin/simple test test/unit/app/duplicate_check/duplicate_check_spec.spl`
2. `bin/simple test test/unit/app/duplicate_check/cache_spec.spl`
3. `bin/simple test test/unit/app/duplicate_check/detector_grouping_spec.spl`
4. `bin/simple test test/unit/app/duplicate_check/phase1_integration_spec.spl`
5. `bin/simple test test/unit/app/duplicate_check/semantic_spec.spl`
6. `bin/simple test test/system/duplicate_check/duplicate_check_regression_system_spec.spl`

## Exit Criteria

This follow-up is complete when all of the following are true:

1. the semantic CLI fixture no longer reports `0 items`
2. semantic mode still falls back cleanly when Ollama is unavailable
3. semantic unit and system regression tests pass
4. the system regression spec asserts positive semantic extraction instead of only non-crashing execution

## Notes

- The currently passing system spec is intentionally conservative and should be treated as an interim guardrail.
- The next implementation pass should prefer observable semantic counts over adding more tolerant assertions.
