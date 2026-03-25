# Team 2: compiler-middle Refactoring Analysis

**Region:** `src/compiler/25.traits/`, `src/compiler/30.types/`, `src/compiler/35.semantics/`, `src/compiler/40.mono/`
**Scope:** ~132 files, ~38.7K lines

---

## 1. FILE_SIZE_VIOLATIONS (>800 lines)

**No files exceed the 800-line limit.** The two known near-limit files remain just under:

| File | Lines | Status |
|------|-------|--------|
| `30.types/variance_types.spl` | 798 | At limit |
| `30.types/dim_constraints.spl` | 779 | At limit |

### Proposed Preventive Splits

#### `variance_types.spl` (798 lines) -- IMMINENT BREACH
Natural split at Phase boundaries (already marked with `# ============================================================================`):
- **`variance_types_core.spl`** (lines 1-275): `Variance` enum, `VarianceOps` class, `TypeParamDef`, `VarianceEnv` (Phase 6A)
- **`variance_types_inference.spl`** (lines 276-520): `HirType` enum, `TypeDef`, `FieldDef`, `MethodDef`, `VarianceInference` (Phase 6B)
- **`variance_types_checking.spl`** (lines 521-798): `SubtypeEnv`, `VarianceChecker`, named test types (Phase 6C)

#### `dim_constraints.spl` (779 lines) -- IMMINENT BREACH
Natural split at section headers:
- **`dim_solver.spl`** (lines 1-450): `DimSolver` struct and all solver methods
- **`dim_runtime.spl`** (lines 451-779): formatting helpers, `WhereClause`, `DimClause`, `RuntimeDimCheck`, `DimCheckGenerator`, `DimCheckTiming`

---

## 2. WATCH_LIST (600-800 lines)

| File | Lines | Risk | Notes |
|------|-------|------|-------|
| `30.types/higher_rank_poly_types.spl` | 721 | HIGH | 10 classes/enums; split Kind+TypeVar vs PolyType+Substitution |
| `30.types/type_infer/inference_expr.spl` | 686 | MEDIUM | Already split ops to separate file; stable |
| `40.mono/monomorphize/deferred.spl` | 670 | MEDIUM | DeferredMonomorphizer (500 lines) dominates; split stats+examples |
| `30.types/simd.spl` | 665 | LOW | Test file (51 test fns); acceptable for test files |
| `30.types/type_system/stmt_check.spl` | 663 | MEDIUM | 24 public fns; split by statement kind |
| `40.mono/monomorphize/partition.spl` | 641 | LOW | Clean section structure |
| `30.types/macro_checker.spl` | 640 | MEDIUM | 27 public fns; split validation vs expansion |
| `30.types/bidirectional_checking.spl` | 626 | MEDIUM | 36 public fns -- high API surface |
| `30.types/higher_rank_poly_tests_quantifier.spl` | 606 | LOW | Test file |
| `30.types/type_infer/inference_control.spl` | 604 | LOW | Stable |

---

## 3. DUPLICATION

The `bin/simple duplicate_check` tool failed (bootstrap binary does not recognize that command). Manual analysis follows.

### 3a. Cross-file Name Duplication

| Cluster | Files | Functions | Resolution |
|---------|-------|-----------|------------|
| `const_keys` | `30.types/const_keys.spl` (38 fns, 522 lines) vs `35.semantics/const_keys.spl` (19 fns, 418 lines) | 30.types has 38 test fns; 35.semantics has 19 integration fns | **Verify**: likely complementary (types=unit tests, semantics=integration). If overlapping logic exists, extract shared helpers to `30.types/const_keys_common.spl` |
| `simd` cluster | `30.types/simd.spl` (51 fns), `simd_vector_types.spl` (46 fns), `simd_platform.spl` (19 fns) vs `35.semantics/simd_check.spl` (26 fns) | Types defines+tests; semantics validates | Acceptable separation. simd.spl is purely tests. |

### 3b. String Concat Pattern Duplication

`error_formatter.spl` has **70 instances** of `output = output + "..."`. This is a repeated pattern that should use a `StringBuilder` or `List<text>.join()` approach.

---

## 4. LAYER_VIOLATIONS

| Source (Layer) | Imports From | Import | Severity |
|----------------|-------------|--------|----------|
| `30.types/type_infer/context.spl` | 35.semantics | `use compiler.semantics.narrowing.*` | **HIGH** |
| `30.types/type_infer/inference_expr_ops.spl` | 35.semantics | `use compiler.semantics.narrowing.*` | **HIGH** |
| `30.types/type_infer/inference_expr.spl` | 35.semantics | `use compiler.semantics.narrowing.*` | **HIGH** |
| `30.types/type_infer_types.spl` | 35.semantics | `use compiler.semantics.narrowing.*` | **HIGH** |
| `30.types/type_infer.spl` | 35.semantics | `use compiler.semantics.narrowing.*` | **HIGH** |

**All 5 violations are the same dependency:** `30.types` -> `35.semantics.narrowing`.

**Resolution:** Move `narrowing.spl` (468 lines) from `35.semantics/` to `30.types/` since it defines type-narrowing data types (`NarrowingCondition`, `NarrowingFact`, `NarrowingScope`, `NarrowingContext`) that are fundamentally part of the type layer. Alternatively, extract the types/enums used by 30.types into a `30.types/narrowing_types.spl` and keep the analysis logic in 35.semantics.

**25.traits and 35.semantics:** Clean. No upward layer violations detected.

---

## 5. COUPLING_HOTSPOTS (Fan-out by import count)

| Imports | File | Notes |
|---------|------|-------|
| 26 | `30.types/associated_types.spl` | Re-export hub -- aggregates all associated_types_* submodules |
| 20 | `30.types/variance.spl` | Re-export hub for variance_* submodules |
| 20 | `30.types/higher_rank_poly.spl` | Re-export hub for higher_rank_* submodules |
| 14 | `30.types/higher_rank_poly_tests_unification.spl` | Test file (acceptable) |
| 12 | `30.types/associated_types_tests_resolve.spl` | Test file |
| 11 | `30.types/type_infer.spl` | Facade -- expected |

The top 3 are **re-export facades** which is a valid pattern. No action needed.

### Public API Surface Hotspots (>15 fns)

| Fns | File | Concern |
|-----|------|---------|
| 51 | `30.types/simd.spl` | Test file, acceptable |
| 46 | `30.types/simd_vector_types.spl` | Type definitions, each type needs constructors |
| 38 | `30.types/const_keys.spl` | Mostly test fns |
| 36 | `30.types/bidirectional_checking.spl` | **Too wide** -- consider grouping by check kind |
| 31 | `30.types/higher_rank_poly_types.spl` | 10 classes, methods on each |
| 27 | `30.types/macro_checker.spl` | **Review**: split validation vs expansion |

---

## 6. BIGO_FLAGS

### 6a. Array Concatenation in Loops (O(n^2))

| File:Line | Pattern | Severity |
|-----------|---------|----------|
| `40.mono/monomorphize/engine.spl:118` | `parts = parts + [concrete_type_to_text(arg)]` | **HIGH** -- in loop over generic args |
| `40.mono/monomorphize/engine.spl:138` | `self.table.pending_functions = self.table.pending_functions + [(key, ...)]` | **MEDIUM** -- grows with each generic instantiation |
| `40.mono/monomorphize/engine.spl:145` | `self.table.processed = self.table.processed + [mangled]` | **MEDIUM** -- same growth pattern |

**Fix:** Use `.push()` for all three.

### 6b. String Concatenation in Loops (O(n^2))

| File:Line | Count | Severity |
|-----------|-------|----------|
| `35.semantics/error_formatter.spl` | 70 instances of `output = output + ...` | **HIGH** -- diagnostic output assembly |
| `30.types/dim_constraints_types.spl:396-407` | `notes_json = notes_json + ...` in loop | **MEDIUM** -- JSON serialization loop |
| `35.semantics/lint/remote_exec_lint.spl:327` | `mmap_buffer = mmap_buffer + " " + trimmed` in loop | **MEDIUM** |

**Fix:** Use `List<text>` + `.join()` or a `StringBuilder` pattern.

### 6c. `.contains()` on Arrays (potential O(n) per call)

| File:Line | Context | Severity |
|-----------|---------|----------|
| `30.types/type_infer/generalization.spl:96,114-115,128-129` | `.contains()` on `scheme.vars`, `env_vars`, `to_generalize` lists | **MEDIUM** -- depends on list size; consider `Set` |
| `30.types/type_system/checker.spl:223,231` | `.contains()` checking struct field keys | **LOW** -- typically small sets |

---

## 7. RECOMMENDATIONS (Prioritized)

### P0 -- Critical (do now)

1. **Fix layer violation:** Move `narrowing.spl` types to `30.types/` or extract `narrowing_types.spl` into `30.types/`. All 5 files in `30.types/type_infer/` depend on it. This is the only architectural violation in the region.

2. **Fix O(n^2) array concat in `engine.spl`:** Replace 3 instances of `arr = arr + [item]` with `.push()`. This is in the monomorphization hot path.

### P1 -- High (this sprint)

3. **Refactor `error_formatter.spl` string building:** 70 `output = output + ...` instances. Use `List<text>` accumulator + `.join("")` at the end.

4. **Split `variance_types.spl` (798 lines):** At the limit. Split into 3 files along Phase 6A/6B/6C boundaries.

5. **Split `dim_constraints.spl` (779 lines):** Split `DimSolver` from runtime check generation.

### P2 -- Medium (next sprint)

6. **Split `higher_rank_poly_types.spl` (721 lines):** Separate Kind+TypeVar from PolyType+Substitution.

7. **Narrow `bidirectional_checking.spl` API:** 36 public fns at 626 lines. Group and consider making helpers private.

8. **Use `Set` in `generalization.spl`:** Replace `List.contains()` checks with `Set` lookups for `env_vars` and `to_generalize`.

### P3 -- Low (backlog)

9. **Fix `dim_constraints_types.spl` JSON serialization:** Replace string concat loop with list+join.

10. **Review `const_keys` duplication:** Verify `30.types/const_keys.spl` (38 fns) and `35.semantics/const_keys.spl` (19 fns) have no logic overlap.

---

## Summary Statistics

| Metric | Count |
|--------|-------|
| Files >800 lines | **0** |
| Files 600-800 (watch) | **10** |
| Layer violations | **5** (all same dependency: 30->35.narrowing) |
| O(n^2) array concat | **3** instances in engine.spl |
| O(n^2) string concat | **70+** instances across 3 files |
| Files with >15 public fns | **20** |
| Coupling hotspots (>10 imports) | **6** (3 are re-export facades) |
