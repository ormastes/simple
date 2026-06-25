# Team 1: Compiler-Frontend Refactoring Analysis
**Region:** `src/compiler/00.common/`, `src/compiler/10.frontend/`, `src/compiler/15.blocks/`, `src/compiler/20.hir/`
**Scope:** ~181 files, ~49,861 lines

---

## 1. FILE_SIZE_VIOLATIONS (>800 lines)

| File | Lines | Proposed Splits |
|------|-------|----------------|
| `10.frontend/core/interpreter/eval_ops.spl` | 1035 | Split into 3 files at existing section markers: **eval_ops_calls.spl** (L21-353: float parsing + call/function/struct constructor, ~333 lines), **eval_ops_methods.spl** (L354-559: method dispatch + array/text methods, ~206 lines), **eval_ops_access.spl** (L559-811: field/index/slice access + literals + assignment, ~252 lines). Remaining lines (L837-1035: return/interpolation/null-coalesce/enum/lambda/comprehensions) stay as **eval_ops.spl** (~198 lines). |
| `10.frontend/core/parser_decls.spl` | 930 | Split at function boundaries: **parser_decls.spl** keeps helpers + fn/extern/struct/enum parsing (L1-481, ~481 lines), **parser_decls_module.spl** gets `parse_module_body()` (L482-853, ~371 lines), **parser_decls_bitfield.spl** gets `parse_bitfield_decl()` (L854-930, ~77 lines). |
| `10.frontend/core/parser_primary.spl` | 850 | Split at function boundaries: **parser_primary.spl** keeps `parse_primary_expr()` (L1-608, ~608 lines), **parser_asm.spl** gets ASM-related parsing: `parse_asm_target_spec`, `parse_int_text`, `parse_asm_match`, `parse_asm_assert_expr` (L609-850, ~242 lines). |
| `20.hir/hir_lowering/items.spl` | 811 | Split the single `impl HirLowering` block: **hir_lower_items_core.spl** (L16-225: lower_module + declare_module_symbols + lower_import, ~210 lines), **hir_lower_items_types.spl** (L226-525: lower_function through lower_bitfield_field + infer_bit_width, ~300 lines), **hir_lower_items_traits.spl** (L554-811: lower_trait through lower_module wrapper + lower_mock_decl, ~258 lines). |

---

## 2. WATCH_LIST (600-800 lines)

| File | Lines | Risk |
|------|-------|------|
| `10.frontend/core/lexer_scanners.spl` | 749 | High -- many `for i in 0..100000` loops |
| `10.frontend/core/ast.spl` | 747 | Medium -- 92 public functions (API surface) |
| `10.frontend/desugar/spawn_analysis.spl` | 740 | Low |
| `10.frontend/core/parser_expr.spl` | 740 | Medium -- highest fan-out (62 imports) |
| `10.frontend/core/interpreter/eval.spl` | 730 | Medium |
| `10.frontend/core/mir.spl` | 716 | High -- 92 public functions (API surface) |
| `10.frontend/core/lexer_struct.spl` | 716 | High -- many `for i in 0..100000` loops |
| `10.frontend/core/lexer.spl` | 689 | Medium -- 69 public functions |
| `10.frontend/core/interpreter/eval_tables.spl` | 683 | Low |
| `10.frontend/core/parser_stmts.spl` | 676 | Medium -- 48 imports |
| `10.frontend/core/interpreter/eval_builtins.spl` | 667 | Low |
| `20.hir/hir_definitions.spl` | 662 | Low |
| `10.frontend/core/__init__.spl` | 660 | Medium -- barrel file, re-exports only |
| `20.hir/hir_lowering/async.spl` | 626 | Low |
| `10.frontend/core/ast_expr.spl` | 600 | High -- 70 public functions |

---

## 3. DUPLICATION

**Note:** The `bin/simple` duplicate_check tool failed (`error: unknown command`). Analysis below is manual.

### Duplicate Filename Clusters

Files sharing the same basename across the 4 layers:

| Basename | Locations | Risk |
|----------|-----------|------|
| `error.spl` | `00.common/error.spl` (513 lines), `10.frontend/core/error.spl` | **High** -- both define error types/formatting. 00.common is comprehensive; core version is "easyfix" suggestions. Consider merging or clear separation. |
| `types.spl` | `10.frontend/core/types.spl` (556 lines), `20.hir/hir_lowering/types.spl` | Medium -- different purposes (frontend type system vs HIR lowering context). Names are fine. |
| `hir_types.spl` | `10.frontend/core/hir_types.spl`, `20.hir/hir_types.spl` (582 lines) | **High** -- both define HIR type tags/kinds. Core version is "seed-compatible" with integer tags; 20.hir version is full HIR type system with SymbolTable. Risk of diverging type definitions. |
| `visibility.spl` | `00.common/dependency/visibility.spl` (466 lines), `10.frontend/...` | Medium -- 00.common has the canonical Lean-verified model; frontend has module visibility auto-public logic. |
| `value.spl` | `10.frontend/core/interpreter/value.spl` (443 lines), `15.blocks/...` | Low -- interpreter arena values vs block-parsed values. Different domains. |

### Estimated Duplication

- **~5 duplicate clusters** identified by filename overlap
- **~200-400 lines** of likely duplicated type/constant definitions across `hir_types.spl` (core vs 20.hir)
- **~100 lines** of error formatting overlap between the two `error.spl` files

### Resolution Proposals

1. **Merge `hir_types.spl`**: Move core HIR type tag constants to `00.common/hir_type_tags.spl`, import from both `10.frontend` and `20.hir`. Eliminates ~200 lines of duplicate integer tag definitions.
2. **Rename `10.frontend/core/error.spl`**: Rename to `easyfix_errors.spl` to clearly distinguish from `00.common/error.spl`.

---

## 4. LAYER_VIOLATIONS

### 00.common -> higher layers (CRITICAL)

| Source File | Imported Module | Direction | Severity |
|-------------|----------------|-----------|----------|
| `00.common/attributes.spl:21` | `compiler.frontend.parser_types` (L10) | 00->10 | **HIGH** -- common depends on frontend AST types |
| `00.common/attributes.spl:22` | `compiler.types.type_layout` (L30) | 00->30 | **HIGH** -- common depends on type system |
| `00.common/compiler_services.spl:15` | `compiler.backend.backend_port` (L70) | 00->70 | **CRITICAL** -- common depends on backend |

**Impact:** These create circular dependency potential. `00.common` should be a leaf layer with zero upward imports.

**Fix:** Extract `Attribute`, `Expr`, `ExprKind`, `LayoutAttr`, `LayoutKind` types into `00.common/` or accept them as parameters rather than importing.

### 10.frontend -> higher layers

| Source File | Imported Module | Direction | Severity |
|-------------|----------------|-----------|----------|
| `10.frontend/frontend.spl:11` | `compiler.tools.desugar_async` (L90) | 10->90 | **HIGH** -- frontend depends on tools layer |
| `10.frontend/treesitter/outline_lexer.spl:12` | `compiler.blocks.blocks.registry` (L15) | 10->15 | **MEDIUM** -- frontend depends on blocks (but 15 is adjacent) |

### 15.blocks -> higher layers

No violations detected. Clean.

### 20.hir -> higher layers

| Source File | Imported Module | Direction | Severity |
|-------------|----------------|-----------|----------|
| `20.hir/hir_lowering/items.spl:11` | `compiler.types.type_layout` (L30) | 20->30 | **MEDIUM** -- HIR depends on type system |
| `20.hir/inference/infer.spl:9` | `compiler.tools.suffix_registry` (L90) | 20->90 | **HIGH** -- HIR depends on tools layer |
| `20.hir/hir_definitions.spl:12` | `compiler.types.type_layout` (L30) | 20->30 | **MEDIUM** -- HIR depends on type system |

**Total violations:** 8 (3 critical/high in 00.common, 2 high in 10/20, 3 medium)

---

## 5. COUPLING_HOTSPOTS (Fan-Out by `use` count)

| File | `use` Count | Assessment |
|------|-------------|------------|
| `10.frontend/core/parser_expr.spl` | 62 | **CRITICAL** -- coupled to nearly everything |
| `10.frontend/core/parser_decls.spl` | 51 | **HIGH** |
| `10.frontend/core/parser_stmts.spl` | 48 | **HIGH** |
| `10.frontend/core/parser_primary.spl` | 41 | HIGH |
| `10.frontend/core/parser.spl` | 39 | HIGH |
| `10.frontend/core/lexer.spl` | 39 | HIGH |
| `10.frontend/core/lexer_scanners.spl` | 24 | Medium |
| `10.frontend/core/lexer_struct.spl` | 20 | Medium |
| `10.frontend/core/ast_clone.spl` | 18 | Medium |

**Pattern:** The parser files dominate fan-out. `parser_expr.spl` at 62 imports is extreme -- it likely imports every token type, AST node constructor, and utility individually. Consider a `parser_prelude.spl` that re-exports common parser symbols.

### Public API Surface Hotspots (>15 public functions)

| File | Public Fns | Assessment |
|------|-----------|------------|
| `10.frontend/core/mir.spl` | 92 | **CRITICAL** -- should be split into constructor/accessor/utility modules |
| `10.frontend/core/ast.spl` | 92 | **CRITICAL** -- same as above |
| `10.frontend/core/ast_expr.spl` | 70 | HIGH |
| `10.frontend/core/lexer.spl` | 69 | HIGH |
| `10.frontend/core/types.spl` | 61 | HIGH |
| `00.common/error.spl` | 55 | HIGH |
| `10.frontend/core/interpreter/value.spl` | 52 | HIGH |
| `15.blocks/blocks/builtin_blocks_math.spl` | 38 | Medium |

---

## 6. BIGO_FLAGS

### Nested Loop with Unbounded Upper Limit (parser_primary.spl)

| File:Line | Pattern | Severity |
|-----------|---------|----------|
| `parser_primary.spl:140+152` | `for ai in 0..100000` containing `for aj in 0..10000` | **CRITICAL** -- O(10^9) worst case. This is the asm block parser: outer loop collects asm lines, inner loop is error recovery. The inner loop will only run on parse errors, but the bounds are excessive. |
| `parser_primary.spl:164` | `for ai in 0..100000` (asm brace block) | HIGH |
| `parser_primary.spl:393,556` | `for i in 0..10000` (comprehension parsing) | Medium |
| `parser_primary.spl:777,823` | `for ai in 0..10000` (asm match arms) | Medium |

### Lexer Unbounded Loops

| File:Line | Pattern | Severity |
|-----------|---------|----------|
| `lexer_scanners.spl:205` | `for i in 0..1000000` | **CRITICAL** -- 1 million iterations max |
| `lexer_scanners.spl:237,320,358,471` | `for i in 0..100000` (4 locations) | HIGH |
| `lexer_struct.spl:136,274,378,481` | `for i in 0..100000` (4 locations) | HIGH |
| `lexer_struct.spl:353` | `for i in 0..10000` | Medium |

**Note:** These loops use `break` on token boundary conditions (EOF/DEDENT/NEWLINE). They simulate `while` loops with large upper bounds, which is a Simple language idiom (no `while` keyword). The bounds are safe in practice but wasteful as iteration limits.

### `.contains()` Inside Loops

| File:Line | Pattern | Severity |
|-----------|---------|----------|
| `core/aop.spl:492,498` | `.contains()` inside `for` loop over advice/rules | **MEDIUM** -- O(n*m) where n=rules, m=used_rules. Acceptable for small AOP rule sets. |
| `core/call_graph.spl:290` | `existing.contains(path)` in loop | MEDIUM -- path dedup. Use a Set. |

### String Concat in Loops

No significant string concatenation in loops found in the frontend region. The `test_hir_lower.spl` hits are counter increments (`count + 1`), not string building.

---

## 7. RECOMMENDATIONS (Prioritized)

### P0 -- Critical (fix before next release)

1. **Fix `00.common` layer violations.** `attributes.spl` importing from `frontend` and `types`, and `compiler_services.spl` importing from `backend`, breaks the foundational layering. Extract the needed types (`Attribute`, `Expr`, `LayoutAttr`, `BackendPort`) into `00.common/` or use trait abstractions.

2. **Reduce nested loop bounds in `parser_primary.spl`.** The `0..100000` / `0..10000` nested pair at lines 140+152 creates a theoretical O(10^9) path. Reduce inner recovery loop to `0..100` and outer asm loop to `0..10000`.

3. **Reduce `lexer_scanners.spl:205` loop bound.** `0..1000000` is excessive for any single scan operation. Reduce to `0..100000` maximum.

### P1 -- High (next sprint)

4. **Split `eval_ops.spl` (1035 lines).** Already has `# =====` section markers. Split into `eval_ops_calls.spl`, `eval_ops_methods.spl`, `eval_ops_access.spl`, keeping remainder in `eval_ops.spl`.

5. **Split `parser_decls.spl` (930 lines).** Extract `parse_module_body()` to `parser_decls_module.spl` and `parse_bitfield_decl()` to `parser_decls_bitfield.spl`.

6. **Create `parser_prelude.spl`** to reduce fan-out. The 5 parser files average 48 imports each. A shared prelude re-exporting common tokens, AST constructors, and parser utilities would reduce coupling.

7. **Fix `20.hir/inference/infer.spl` -> `compiler.tools` violation.** Move `SuffixRegistry` to `00.common/` or `20.hir/`.

8. **Fix `10.frontend/frontend.spl` -> `compiler.tools` violation.** Move `desugar_async` into `10.frontend/desugar/`.

### P2 -- Medium (backlog)

9. **Merge HIR type tag constants.** Both `10.frontend/core/hir_types.spl` and `20.hir/hir_types.spl` define HIR type kind integer tags. Extract shared constants to `00.common/hir_type_tags.spl`.

10. **Split `parser_primary.spl` (850 lines).** Extract ASM parsing functions (lines 609-850) to `parser_asm.spl`.

11. **Reduce public API surface** of `ast.spl` (92 fns) and `mir.spl` (92 fns). Group into sub-modules: constructors, accessors, utilities.

12. **Rename `10.frontend/core/error.spl`** to `easyfix_errors.spl` to avoid confusion with `00.common/error.spl`.

### P3 -- Low (opportunistic)

13. **Split `hir_lowering/items.spl` (811 lines).** The single `impl HirLowering` block has clear method groups. Split by lowered item type.

14. **Monitor watch list files** approaching 800 lines: `lexer_scanners.spl` (749), `ast.spl` (747), `spawn_analysis.spl` (740), `parser_expr.spl` (740).

15. **Replace `.contains()` with Set lookups** in `call_graph.spl:290` and `aop.spl:492`.
