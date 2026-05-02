# Team 4: compiler-driver Refactoring Analysis Report

Region: `src/compiler/80.driver/`, `85.mdsoc/`, `90.tools/`, `95.interp/`, `99.loader/` (~451 files, ~64K lines)

---

## 1. FILE_SIZE_VIOLATIONS (>800 lines)

| File | Lines | Proposed Splits |
|------|-------|----------------|
| `90.tools/lint/main.spl` | 974 | **lint_config.spl** (L1-130: LintLevel, LintConfig, parse_lint_level, build_default_levels), **lint_rules.spl** (L412-499: Linter.new with all lint rule definitions), **lint_checks.spl** (L500-810: check methods - TODO format, unfold, SDN write), **lint_main.spl** (L830-975: CLI entry, fix collection, fix application) |
| `80.driver/driver.spl` | 895 | **driver_phases.spl** (L390-520: lower_to_hir, lower_to_hir_impl, resolve_methods_impl -- standalone compatibility methods), **driver_mir.spl** (L760-880: lower_to_mir, borrow_check, process_async, optimize_mir). Keep core CompilerDriver class + compile() in driver.spl (~400 lines). |
| `80.driver/build/bootstrap_pipeline.spl` | 785 | **bootstrap_stages.spl** (L50-530: individual run_check/run_bootstrap/run_build/run_seed/run_core1/run_core2/run_full1/run_full2 functions), **bootstrap_orchestrator.spl** (L555-785: Pipeline class, verify_reproducibility, PipelineResult). Keep config/types in bootstrap_pipeline.spl (~50 lines). |

### Internal Duplication in `driver.spl`

`lower_to_hir_impl()` (L493-502) is a simplified duplicate of the main `lower_to_hir()` method (L398-487). The `_impl` version is 10 lines and skips visibility checking, static assertions, type inference, trait coherence, and effect inference. Comment says "kept for compatibility" -- should be deleted or callers migrated to the full version.

---

## 2. WATCH_LIST (600-800 lines)

| File | Lines | Risk |
|------|-------|------|
| `95.interp/mir_interpreter.spl` | 748 | Near limit; large match/dispatch logic |
| `99.loader/loader/compiler_ffi.spl` | 734 | Near limit; FFI bridge functions |
| `90.tools/ffi_gen/main.spl` | 732 | Near limit; code generation logic |
| `90.tools/query_api.spl` | 712 | Query API surface |
| `90.tools/formatter/main.spl` | 704 | Formatter implementation |
| `90.tools/ffi_gen/specs/runtime_value_full.spl` | 656 | FFI spec definitions |
| `90.tools/migrate/tests.spl` | 629 | Test migration tool |
| `80.driver/smf_writer.spl` | 618 | SMF generation |
| `99.loader/module_resolver/resolution.spl` | 609 | Module resolution logic |

---

## 3. DUPLICATION

### 3a. Cross-Team Duplicate (CONFIRMED IDENTICAL)

`src/compiler/80.driver/build/bootstrap_pipeline.spl` (785 lines) is **byte-identical** to `src/app/build/bootstrap_pipeline.spl` (785 lines). `diff` produced no output.

**Resolution:** The canonical copy should be `src/app/build/bootstrap_pipeline.spl` since it is an application-level build orchestration concern, not a compiler-internal concern. The `80.driver` copy should be replaced with a re-export:
```
# src/compiler/80.driver/build/bootstrap_pipeline.spl
use app.build.bootstrap_pipeline.*
```

### 3b. `ffi_gen/specs/im_rs.spl` -- Dead Code Assessment

- 276 lines, **25 `pass_todo` markers**, **zero** implemented functions
- Every function body is `pass_todo("Rust FFI bridge not built")`
- Covers HashMap, Vector, HashSet from the `im` crate
- **Verdict: Dead code / placeholder spec.** No FFI bridge exists. Should be either (a) deleted entirely, or (b) moved to a `specs/pending/` directory to signal intent without polluting the active codebase.

### 3c. Internal Duplication Patterns

| Pattern | Location A | Location B | Lines |
|---------|-----------|-----------|-------|
| `lower_to_hir_impl` (simplified copy) | driver.spl L398 (full) | driver.spl L493 (simplified) | ~90 vs ~10 |
| `hash_map[key] = existing + [block]` list-append pattern | detector.spl L198-205 | detector.spl L286-291 | ~7 each |
| `files = files + [item]` accumulation | fix/imports.spl, migrate/tests.spl, verify/verify_features.spl, duplicate_check/*.spl | (repeated across 8+ files) | ~20 total |

---

## 4. LAYER_VIOLATIONS

| Source | Import | Direction | Severity |
|--------|--------|-----------|----------|
| `80.driver/build/doc_warnings.spl` | `compiler.mdsoc.types`, `compiler.mdsoc.layer_checker` | 80 -> 85 | **Medium** -- doc warnings need MDSOC layer info |
| `80.driver/build/duplication.spl` | `compiler.tools.duplicate_check.*` (config, detector, formatter, cache) | 80 -> 90 | **Medium** -- build delegates to tools |
| `80.driver/driver_api.spl` | `compiler.tools.async_integration` | 80 -> 90 | **Low** -- async integration is cross-cutting |
| `80.driver/driver_types.spl` | `compiler.tools.aop` | 80 -> 90 | **Low** -- AOP weaving is cross-cutting |
| `80.driver/driver.spl` | `compiler.tools.async_integration` | 80 -> 90 | **Low** -- same as driver_api |

**85.mdsoc -> 90+**: None found (clean).
**90.tools -> 95+**: None found (clean).
**95.interp -> 99+**: None found (clean).

**Assessment:** The 80 -> 85 and 80 -> 90 violations are all from driver/build calling into tools and MDSOC layers. This is architecturally expected for a driver layer that orchestrates everything. The pattern is "driver delegates to tools" which is correct. However, the dependency could be inverted: tools should expose a facade interface that the driver calls, rather than the driver importing tool internals directly.

---

## 5. COUPLING_HOTSPOTS

### Highest Fan-Out Files (import count)

| File | Import Count | Assessment |
|------|-------------|------------|
| `80.driver/driver.spl` | **27** | Imports from hir, mir, frontend, backend, codegen, types, mono, mir_opt, tools, borrow, traits, semantics, common, driver sub-modules. Expected for orchestrator but very high. |
| `80.driver/driver_api.spl` | **24** | Public API surface -- aggregates all driver capabilities |
| `80.driver/driver_types.spl` | **17** | Type definitions importing from many layers |
| `80.driver/build/main.spl` | **15** | Build command dispatcher |
| `90.tools/ffi_gen/specs/__init__.spl` | **14** | Aggregates all FFI specs |
| `90.tools/ffi_gen/main.spl` | **14** | FFI generator imports |
| `80.driver/build/cli_entry_full.spl` | **14** | CLI entry point |

### `driver.spl` Full Import Analysis

`driver.spl` imports from **11 distinct compiler layers**:
- `compiler.hir` (hir, hir_lowering, hir_types)
- `compiler.mir` (mir)
- `compiler.frontend` (frontend)
- `compiler.backend` (backend, codegen, ffi, linker, cmake_gen)
- `compiler.types` (type_infer, type_system)
- `compiler.mono` (monomorphize_integration)
- `compiler.mir_opt` (mir_opt_integration)
- `compiler.tools` (async_integration)
- `compiler.borrow` (borrow_check)
- `compiler.traits` (trait_coherence, trait_validation)
- `compiler.semantics` (visibility_integration, const_eval)
- `compiler.common` (config)
- `compiler.driver` (driver_types, smf_writer, driver_aot_output, cache)

**Facade Recommendation:** Create `compiler.driver.pipeline_facade.spl` that re-exports a simplified pipeline interface (`parse -> lower -> check -> optimize -> codegen -> link`) with each phase hiding its layer imports. `driver.spl` would then import only from `pipeline_facade` instead of 11 layers directly. This reduces coupling from 27 imports to ~5.

---

## 6. BIGO_FLAGS

| File:Pattern | Issue | Severity |
|-------------|-------|----------|
| `duplicate_check/detector.spl:229-244` | **Bubble sort** O(n^2) on duplicate groups by impact score | **High** -- use merge sort or sorted insert |
| `duplicate_check/detector.spl:198-206` | `existing + [block]` creates new list each append -- O(n^2) total for n blocks | **High** -- use `.push()` instead |
| `duplicate_check/detector.spl:302` | `limited = limited + [fblocks[round]]` in sampling loop -- O(n^2) | **Medium** -- use `.push()` |
| `duplicate_check/detector.spl:350` | `feature_vectors = feature_vectors + [feature_vec]` in while loop -- O(n^2) | **Medium** -- use `.push()` |
| `duplicate_check/detector.spl:358` | `refined_groups = refined_groups + [group]` in loop -- O(n^2) | **Medium** -- use `.push()` |
| `fix/imports.spl:37,40` | `new_lines = new_lines + [line]` per line -- O(n^2) for file with n lines | **Medium** |
| `migrate/tests.spl:23,41` | `files = files + [trimmed]` -- O(n^2) for n files | **Low** (small n expected) |
| `lint/main.spl:129,227` | `ALL_LINT_NAMES.contains(name)` linear scan of 18-element array | **Negligible** (n=18 constant) |
| `lint/main.spl:699,724` | `todo_areas.contains(area)`, `todo_priorities.contains(priority)` | **Negligible** (n=13,8 constant) |
| `formatter/main.spl:493` | `while result.contains("  ")` -- repeated string scan to collapse whitespace | **Low** -- could be O(n*m) for pathological input |

### Critical Pattern: `list = list + [item]` Anti-Pattern

Found in **8+ files** across `90.tools/`. Each `+ [item]` allocates a new list and copies all elements. In a loop of n iterations, this is O(n^2) total work. All instances should be converted to `.push()` which is O(1) amortized.

---

## 7. RECOMMENDATIONS (Prioritized)

### P0 -- Critical (fix immediately)

1. **Replace `list + [item]` with `.push()` across 90.tools/** -- O(n^2) -> O(n) in duplicate_check/detector.spl, fix/imports.spl, migrate/tests.spl, verify/verify_features.spl, duplicate_check/benchmark.spl, duplicate_check/doc_extractor.spl, duplicate_check/formatter.spl. ~20 instances total.

2. **Replace bubble sort in detector.spl:229-244** with stdlib sort or at minimum insertion sort. Current O(n^2) comparisons with O(n^2) swaps.

### P1 -- High (next sprint)

3. **Deduplicate bootstrap_pipeline.spl** -- Delete `src/compiler/80.driver/build/bootstrap_pipeline.spl`, replace with re-export from `src/app/build/bootstrap_pipeline.spl`. Eliminates 785 lines of exact duplication.

4. **Split lint/main.spl** (974 lines) into 4 files: lint_config, lint_rules, lint_checks, lint_main. Natural boundaries at L130, L412, L830.

5. **Split driver.spl** (895 lines) -- Extract `lower_to_hir_impl` and `resolve_methods_impl` compat methods into `driver_compat.spl` or delete them. Extract MIR phase methods into `driver_mir.spl`.

### P2 -- Medium (backlog)

6. **Delete or move im_rs.spl** -- 276 lines, 25 pass_todo, zero implementation. Dead code.

7. **Create pipeline_facade.spl** -- Reduce driver.spl's 27 imports / 11-layer fan-out with a facade pattern.

8. **Split bootstrap_pipeline.spl** (785 lines, whichever copy remains) into stages + orchestrator.

9. **Monitor watch-list files** -- 9 files in 600-748 range approaching the 800-line limit.

### P3 -- Low (opportunistic)

10. **Invert tool dependencies** -- Instead of 80.driver importing 90.tools internals, define tool interfaces in 80.driver that 90.tools implements.

11. **Delete `lower_to_hir_impl`** compat method in driver.spl -- It is a dangerous simplified copy that skips safety checks. Callers should use the full `lower_to_hir()`.
