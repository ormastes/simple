# Coupling Analysis — Known Limitations

**Related:** [Requirement](../requirement/coupling_analysis.md) | [Research](../research/coupling_analysis.md) | [Plan](../plan/coupling_analysis.md)

---

## Limitation Summary

| # | Description | Severity | Workaround | Related |
|---|-------------|----------|------------|---------|
| 1 | LCOM4 not wired into CLI — placeholder empty list | High | Call `compute_lcom4()` directly with manually constructed `ClassInfo` | AC-13 |
| 2 | API quality metrics (PSS, EUR, entropy) not wired into CLI — placeholder empty list | High | Call `compute_api_quality()` directly with manually constructed `MethodUsage` data | AC-14, AC-15, AC-16, AC-17 |
| 3 | ATSS not wired into CLI — placeholder empty list | High | Call `check_atss()` directly with manually constructed function registries | AC-20 |
| 4 | RFC metric not implemented | Medium | Use CBO (fan-out) as approximate proxy | AC-05 |
| 5 | CBO equals fan-out (no distinction) | Low | Acceptable simplification for import-level analysis | AC-01 |
| 6 | Abstractness requires caller-supplied trait/type counts | Medium | Pass `trait_counts` and `type_counts` dicts to `compute_all_metrics_with_abstractions()` | AC-11, AC-12 |
| 7 | SCC uses Kosaraju's algorithm, not Tarjan's | Low | Both produce correct results; no functional impact | AC-02 |
| 8 | `format_f64` uses truncation, not rounding | Low | Displayed values may differ from true value by up to 1 ULP in last decimal | AC-01, AC-07 |
| 9 | LCOM4 `fields_share_access` is O(n*m) quadratic per method pair | Low | Only problematic for classes with hundreds of methods and fields; typical classes are small | AC-13 |
| 10 | Layer number extraction is heuristic string parsing | Low | Relies on directory naming convention `NN.name`; non-standard names default to layer 999 | AC-03 |
| 11 | Lint rules W0509 and W0510 defined but not automatically triggered | Medium | Lint coupling rules require coupling analysis data passed in; not auto-run during `build lint` | AC-24 |
| 12 | Relaxed tokenizer and gap matcher are standalone — not integrated into `duplicate_check/` | Medium | Use `find_relaxed_duplicates()` and `find_with_gap_tolerance()` from coupling module directly | AC-22, AC-23 |
| 13 | Entropy returns 0.0 for single-method or zero-usage modules | Low | By design — entropy is undefined for k <= 1; documented as "no external usage" | AC-16 |
| 14 | API Complexity Index uses hardcoded weights, no z-score normalization | Medium | Weights are fixed (0.3, 0.2, 0.1, 0.2, 0.2); z-score requires full population stats not yet collected | AC-17 |
| 15 | DSM matrix can be large for full codebase (2600+ modules) | Low | Use `--layers` or filter to compiler modules; text output may be unwieldy for >50 modules | AC-04, AC-10 |
| 16 | No `--api` or `--lcom` CLI output in practice | High | Flags are parsed but produce empty output since data is not wired in (see #1, #2) | AC-19 |

---

## Detailed Analysis

### 1. LCOM4 not wired into CLI (High)

**File:** `src/compiler/90.tools/coupling/main.spl`

In `run_coupling_analysis()`, LCOM results are initialized as an empty list:
```
# LCOM (computed separately per class — placeholder empty for CLI without AST context)
var lcom_results: [LCOMResult] = []
```

The `compute_lcom4()` function in `lcom.spl` is fully implemented and tested (with doctests), but it requires `MethodFieldAccess` data (which fields each method accesses, which methods it calls). This data must be extracted from the AST or HIR during compilation, and no such extraction pass currently exists in the compiler pipeline.

**Impact:** `--lcom` flag produces no output. Lint rule W0505 (high LCOM) will never fire.

### 2. API Quality Metrics not wired into CLI (High)

**File:** `src/compiler/90.tools/coupling/main.spl`

```
# API quality (placeholder empty for CLI without call-site data)
var api_metrics: [PublicAPIMetrics] = []
```

Computing EUR and entropy requires scanning all call expressions across the codebase to count external callers per public method. This requires either a post-resolution pass over all resolved call expressions or hooking into the compiler's name resolution phase. Neither integration exists yet.

PSS and public ratio could theoretically be computed from the symbol table and visibility system alone, but the current implementation bundles them with EUR/entropy in a single `compute_api_quality()` function that expects all data upfront.

**Impact:** `--api` flag produces no output. Lint rules W0506 (high public surface), W0507 (dead public API), W0508 (high complexity) will never fire.

### 3. ATSS not wired into CLI (High)

**File:** `src/compiler/90.tools/coupling/main.spl`

```
# ATSS (placeholder empty — needs AST declaration indices)
var atss_warnings: [ATSSWarning] = []
```

The ATSS implementation in `atss.spl` is complete (sorted type vectors, hash-based exact grouping, deletion variant generation, edit distance computation). However, it needs function declaration data (parameter names and types per function) extracted from the AST. No extraction pass feeds this data into the coupling CLI.

**Impact:** ATSS warnings never appear. Lint rule W0509 will never fire.

### 4. RFC Metric Not Implemented (Medium)

**Files:** `src/compiler/90.tools/coupling/metrics.spl`

The `CouplingMetrics` struct does not include an RFC field. The requirement (AC-05) calls for RFC (Response For Class) = methods + directly called external methods. This requires call graph data from `src/compiler/10.frontend/core/call_graph.spl`, which is not integrated into the coupling module.

### 5. CBO Equals Fan-Out (Low)

**File:** `src/compiler/90.tools/coupling/metrics.spl`

In the implementation, CBO is set to `fo` (fan-out):
```
cbo: fo,
```

In the CK metric suite, CBO counts distinct classes/modules that a class is coupled to (both incoming and outgoing). The implementation only counts outgoing dependencies (fan-out). For import-level module analysis this is a reasonable simplification, but it differs from the canonical CK definition.

### 6. Abstractness Requires External Data (Medium)

**File:** `src/compiler/90.tools/coupling/metrics.spl`

`compute_all_metrics()` (without abstractions) sets abstractness and distance to 0.0 for all modules. The `compute_all_metrics_with_abstractions()` variant requires caller-supplied `trait_counts` and `type_counts` dictionaries. No part of the pipeline currently extracts these counts from the compiler's type system.

### 7. SCC Algorithm Mismatch (Low)

**File:** `src/compiler/90.tools/coupling/metrics.spl`

The doc comment says "Kosaraju's algorithm" and the implementation calls `graph_strongly_connected_components()` from the stdlib graph library (which uses Kosaraju's). The requirement originally specified Tarjan's. Both are O(V+E) and produce identical results. Updated AC-02 to accept either algorithm.

### 8. Float Formatting Truncation (Low)

**File:** `src/compiler/90.tools/coupling/api_quality.spl`

`format_f64()` uses integer truncation (`(val_f * multiplier).to_i64()`) rather than rounding. For example, `0.9999` formatted to 2 decimals shows `0.99` instead of `1.00`. This affects display only, not computation.

### 9. Quadratic Field Comparison in LCOM4 (Low)

**File:** `src/compiler/90.tools/coupling/lcom.spl`

`fields_share_access()` does a nested loop over two field-access lists (O(n*m)). This is called for every pair of methods in a class, making the total complexity O(M^2 * F^2) per class where M = methods and F = average fields accessed per method. For typical classes (< 30 methods, < 10 fields each), this is negligible. For very large classes it could be slow; a hash-set approach would reduce to O(M^2 * F).

### 10. Heuristic Layer Parsing (Low)

**File:** `src/compiler/90.tools/coupling/layer_check.spl`

`try_parse_layer_segment()` parses layer numbers from path segments by looking for leading digits. It handles standard patterns like `"00.common"` and `"10.frontend"` but may misparse unusual directory names with leading digits that are not layer prefixes. Non-layer modules get layer 999 for sorting purposes.

### 11. Lint Rules Not Auto-Triggered (Medium)

**File:** `src/compiler/35.semantics/lint/coupling.spl`

The coupling lint rules (W0501-W0510) are defined as standalone functions (`check_high_cbo()`, `check_circular_deps()`, etc.) that take coupling analysis results as input. They are not registered in the standard lint pass (`src/compiler/35.semantics/lint/__init__.spl`) because they require data from the coupling analysis tool, which runs separately from the normal lint pipeline.

### 12. Relaxed/Gap Detection Not Integrated into duplicate_check (Medium)

**Files:** `src/compiler/90.tools/coupling/relaxed_tokenizer.spl`, `src/compiler/90.tools/coupling/gap_matcher.spl`

The plan called for extending `src/app/duplicate_check/tokenizer.spl` with relaxed mode and `src/app/duplicate_check/detector.spl` with gap tolerance. Instead, separate implementations were created in the coupling module. The existing `duplicate_check/` app's `DuplicationConfig` was not extended with `relaxed` and `gap_tolerance` fields as planned.

### 14. API Complexity Index — No Z-Score (Medium)

**File:** `src/compiler/90.tools/coupling/api_quality.spl`

The requirement and research docs specify z-score normalization across all modules for the API Complexity Index. The implementation uses raw weighted sums without z-score normalization, which means the index is not comparable across different codebases or analysis runs of different sizes.

### 15. Large DSM Output (Low)

**File:** `src/compiler/90.tools/coupling/dsm.spl`

For the full Simple compiler codebase (~2600 files), the DSM matrix would be ~2600x2600. The text and markdown formatters produce tables that would be impractical to read at this scale. The implementation works correctly but is only useful when scoped to a subset of modules.
