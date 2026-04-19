# Duplicate Check Regression System Test Plan

## Scope

Executable regression coverage for the duplicate-check refactor, focused on:

- CLI execution against a real temporary workspace
- Grouping stability for repeated duplicates across multiple files
- Noise suppression for low-signal export-only boilerplate
- Incremental cache invalidation after source changes
- Semantic mode fallback when Ollama is unavailable

## Scenarios

1. CLI exact grouping
   Expected: text report lists one duplicate group and three occurrences, process exits non-zero because duplicates exceed `max_allowed`.

2. Noise suppression
   Expected: cosine-enabled JSON report returns zero groups for export-only boilerplate.

3. Semantic fallback
   Expected: semantic mode reports the text-based fallback banner and still emits a similar-docs result when documentation is duplicated.

4. Incremental cache invalidation
   Expected: cached blocks load on the second read, unchanged files skip reprocessing, and modified files require reprocessing after mtime advances.

## Coverage Artifact

- System spec: `test/system/duplicate_check/duplicate_check_regression_system_spec.spl`
- Supporting unit specs:
  - `test/unit/app/duplicate_check/duplicate_check_spec.spl`
  - `test/unit/app/duplicate_check/phase1_integration_spec.spl`
