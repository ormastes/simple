# Standard Library Utils Refactoring Plan

**Date:** 2026-02-12
**Status:** Planning
**Scope:** 78 stdlib `*_utils.spl` files (800-2434 lines each)

---

## Executive Summary

Found **78 stdlib utility files** averaging 1,100 lines that can be refactored using the facade pattern. These are pure function collections with clear module boundaries, unlike compiler impl blocks.

**Target:** Split into focused modules of 200-400 lines each.

---

## Non-Splittable Files (Document Only)

These files have large impl blocks that cannot be split in Simple:

| File | Lines | Reason |
|------|-------|--------|
| `compiler/parser.spl` | 2,453 | Large impl Parser block |
| `compiler_core_legacy/parser.spl` | 2,322 | Large impl Parser block |
| `app/compile/c_translate.spl` | 1,871 | Large impl CTranslator block |
| `compiler_core_legacy/parser.spl` | 1,862 | Large impl Parser block |
| `app/mcp/main.spl` | 1,854 | Complex MCP server orchestration |
| `compiler/treesitter/outline.spl` | 1,823 | Large impl TreeSitter block |
| `compiler_core_legacy/interpreter/eval.spl` | 1,619 | Large impl Interpreter block |
| `compiler/mir_lowering.spl` | 1,503 | Large impl MirLowering block |
| `compiler/lexer.spl` | 1,430 | Large impl Lexer block |

**Recommendation:** Document as technical debt per CLAUDE.md. Wait for language support for split impl blocks.

---

## Priority 1: Critical Size (2000+ lines) - 4 files

### 1. numerical_methods_utils.spl (2,434 lines)

**Structure:** Pure function collection, 11 categories

**Refactoring:**
```
src/lib/numerical_methods/
├── mod.spl (80 lines) - Re-exports
├── root_finding.spl (~250 lines)
│   - bisection, newton_raphson, secant, brent
├── integration.spl (~280 lines)
│   - trapezoidal, simpson, romberg, gaussian_quad
├── differentiation.spl (~180 lines)
│   - finite_differences, richardson_extrapolation
├── interpolation.spl (~300 lines)
│   - linear, lagrange, newton, cubic_spline
├── ode_solvers.spl (~320 lines)
│   - euler, runge_kutta (rk2, rk4), adams_bashforth
├── linear_systems.spl (~280 lines)
│   - gauss_elimination, lu_decomp, iterative_methods
├── eigenvalues.spl (~220 lines)
│   - power_iteration, qr_algorithm
├── polynomials.spl (~180 lines)
│   - horner_eval, roots, derivatives
├── curve_fitting.spl (~150 lines)
│   - least_squares, polynomial_fitting
├── special_functions.spl (~120 lines)
│   - factorial, binomial, gamma_approx
└── error_analysis.spl (~100 lines)
    - absolute_error, relative_error, condition_number
```

### 2. json_parser_utils.spl (2,240 lines)

**Structure:** JSON parser/serializer, 8 categories

**Refactoring:**
```
src/lib/json/
├── mod.spl (80 lines) - Re-exports
├── types.spl (~120 lines)
│   - Constructors: json_null, json_boolean, json_number, json_string
├── parser.spl (~400 lines)
│   - json_parse, json_tokenize, parse_value, parse_object, parse_array
├── serializer.spl (~250 lines)
│   - json_serialize, json_pretty, json_format, json_stringify
├── object_ops.spl (~320 lines)
│   - get, set, has, remove, keys, values, entries, merge, map, filter
├── array_ops.spl (~380 lines)
│   - get, set, append, insert, remove, map, filter, reduce, slice
├── path_ops.spl (~180 lines)
│   - get_path, set_path, has_path, delete_path
├── validation.spl (~220 lines)
│   - validate_schema, type_check, is_valid, deep_equals
└── utilities.spl (~210 lines)
    - escape_string, unescape_string, deep_clone, flatten, merge_deep
```

### 3. graph_utils.spl (2,068 lines)

**Structure:** Graph algorithms

**Refactoring:**
```
src/lib/graph/
├── mod.spl (70 lines)
├── types.spl (~150 lines) - Graph, Node, Edge representations
├── traversal.spl (~280 lines) - BFS, DFS, topological_sort
├── shortest_path.spl (~320 lines) - Dijkstra, Bellman-Ford, Floyd-Warshall
├── spanning_tree.spl (~250 lines) - Kruskal, Prim
├── flow.spl (~280 lines) - Max flow, min cut algorithms
├── matching.spl (~220 lines) - Bipartite matching
├── strongly_connected.spl (~180 lines) - Tarjan, Kosaraju
├── coloring.spl (~150 lines) - Graph coloring algorithms
└── utilities.spl (~170 lines) - Common graph operations
```

### 4. gzip_utils.spl (1,891 lines)

**Structure:** Gzip compression/decompression

**Refactoring:**
```
src/lib/compression/gzip/
├── mod.spl (60 lines)
├── types.spl (~120 lines) - Header, block types
├── deflate.spl (~400 lines) - DEFLATE compression
├── inflate.spl (~380 lines) - DEFLATE decompression
├── huffman.spl (~320 lines) - Huffman coding
├── lz77.spl (~280 lines) - LZ77 compression
├── header.spl (~150 lines) - Gzip header parsing
├── crc.spl (~100 lines) - CRC32 checksums
└── stream.spl (~150 lines) - Stream utilities
```

---

## Priority 2: High Priority (1500-2000 lines) - 10 files

| File | Lines | Categories | Modules |
|------|-------|------------|---------|
| `b_tree_utils.spl` | 1,847 | B-tree ops | 6 modules |
| `fenwick_tree_utils.spl` | 1,792 | Fenwick tree | 5 modules |
| `html_parser_utils.spl` | 1,769 | HTML parsing | 7 modules |
| `red_black_tree_utils.spl` | 1,764 | RB-tree ops | 6 modules |
| `rsa_utils.spl` | 1,759 | RSA crypto | 7 modules |
| `avro_utils.spl` | 1,738 | Avro format | 6 modules |
| `file_system_utils.spl` | 1,695 | File ops | 8 modules |
| `regex_engine_utils.spl` | 1,686 | Regex engine | 8 modules |
| `crypto_utils.spl` | 1,677 | Crypto ops | 9 modules |
| `optimization_utils.spl` | 1,664 | Optimization | 7 modules |

---

## Priority 3: Medium Priority (1200-1500 lines) - 18 files

Examples include:
- `linear_algebra_utils.spl` (1,648)
- `cert_utils.spl` (1,621)
- `compression_utils.spl` (1,606)
- `xml_utils.spl` (1,592)
- And 14 more...

---

## Priority 4: Standard Priority (800-1200 lines) - 46 files

Files close to or just over the 800-line threshold.

---

## Implementation Strategy

### Phase 1: Prove Pattern (Week 1)
**Goal:** Refactor 1 file to establish pattern

**Target:** `numerical_methods_utils.spl` (largest, clear categories)

**Steps:**
1. Read full file and map categories
2. Create module structure
3. Extract functions by category
4. Create facade with re-exports
5. Test all imports
6. Backup original

**Success criteria:**
- All tests pass
- Imports unchanged
- Each module < 400 lines

### Phase 2: Critical Files (Week 2-3)
**Goal:** Refactor remaining 3 critical files (2000+ lines)

**Targets:**
- `json_parser_utils.spl`
- `graph_utils.spl`
- `gzip_utils.spl`

**Parallel execution:** Can be done concurrently

### Phase 3: High Priority (Week 4-5)
**Goal:** Refactor 10 high-priority files (1500-2000 lines)

**Batch approach:** 2-3 files per day

### Phase 4: Medium Priority (Week 6-7)
**Goal:** Refactor 18 medium-priority files (1200-1500 lines)

### Phase 5: Standard Priority (Week 8-10)
**Goal:** Refactor remaining 46 files (800-1200 lines)

**Optional:** Only split files that have clear module boundaries

---

## Facade Pattern Template

```simple
# Original file: some_utils.spl (facade)
#
# This file was refactored from 1,500 lines into focused modules.
# See some/ directory for implementations.
#
# Facade Pattern: Import all submodules and re-export public API

# Import submodules
mod some.category1
mod some.category2
mod some.category3

# Re-export all public APIs
export *  # Or explicit exports
```

```simple
# New module: some/category1.spl
#
# Purpose: Brief description of what this category handles
#
# Contains: list of main functions

# ... implementation ...
export *
```

---

## Automation Script

Create helper to speed up refactoring:

```simple
# script: bin/simple refactor-utils <file>
#
# Auto-generates module structure from comments/sections
```

---

## Testing Strategy

For each refactored file:

1. **Module load test:**
   ```bash
   bin/simple build  # Check all modules load
   ```

2. **Import compatibility:**
   ```bash
   # All existing imports should still work
   bin/simple test --grep "import.*<module>"
   ```

3. **Function tests:**
   ```bash
   # Run tests for the refactored module
   bin/simple test test/std/<module>_spec.spl
   ```

4. **Full test suite:**
   ```bash
   bin/simple test  # Everything should pass
   ```

---

## Metrics & Success Criteria

### Current State
| Metric | Value |
|--------|-------|
| Files ≥800 lines | 134 |
| Non-splittable | 10 (impl blocks) |
| Splittable utils | 78 |
| Average utils size | 1,100 lines |
| Largest utils | 2,434 lines |

### Target State
| Metric | Target |
|--------|--------|
| Files ≥800 lines | 10 (impl blocks only) |
| Utils facade size | ~60-80 lines |
| Module size | 200-400 lines average |
| Modules created | ~400 new modules |

### KPIs
- **Code navigation:** Find functions by category, not line number
- **Module clarity:** Each module has single clear purpose
- **Maintainability:** Changes isolated to specific modules
- **Testing:** Can test specific categories independently

---

## Risk Mitigation

### Risks
1. **Breaking imports** - Facade pattern prevents this
2. **Missing functions** - Export * ensures all functions available
3. **Module cycles** - Careful dependency design
4. **Test failures** - Test after each file

### Mitigations
1. **Use facade pattern** - 100% backward compatible
2. **Create backups** - `.backup` extension for originals
3. **Test continuously** - Run tests after each refactoring
4. **Use jj not git** - Easy to undo changes

---

## Estimated Effort

| Phase | Files | Effort | Timeline |
|-------|-------|--------|----------|
| Phase 1 (prove) | 1 | 4 hours | Week 1 |
| Phase 2 (critical) | 3 | 12 hours | Week 2-3 |
| Phase 3 (high) | 10 | 20 hours | Week 4-5 |
| Phase 4 (medium) | 18 | 24 hours | Week 6-7 |
| Phase 5 (standard) | 46 | 40 hours | Week 8-10 |
| **Total** | **78 files** | **100 hours** | **10 weeks** |

**Quick win option:** Phase 1-2 (4 largest files) = 16 hours = ~40% of value

---

## Recommendations

### Option A: Quick Win (Recommended)
**Target:** 4 critical files (2000+ lines)
**Effort:** 16 hours
**Impact:** ~8,500 lines → ~400 modules
**Timeline:** 2-3 weeks

### Option B: High Impact
**Target:** 14 critical+high files (1500+ lines)
**Effort:** 36 hours
**Impact:** ~24,000 lines → ~1,000 modules
**Timeline:** 5 weeks

### Option C: Complete
**Target:** All 78 utils files
**Effort:** 100 hours
**Impact:** ~86,000 lines → ~4,000 modules
**Timeline:** 10 weeks

---

## Next Steps

1. **Get approval** for refactoring approach
2. **Start with Phase 1:** `numerical_methods_utils.spl`
3. **Create automation** to speed up phases 3-5
4. **Document non-splittable files** as technical debt
5. **Track progress** in this document

---

## Technical Debt Documentation

### Files That CANNOT Be Split

Document these in `doc/technical_debt/large_impl_blocks.md`:

| File | Lines | Reason | Recommendation |
|------|-------|--------|----------------|
| compiler/parser.spl | 2,453 | Large impl Parser | Wait for language support |
| compiler_core_legacy/parser.spl | 2,322 | Large impl Parser | Wait for language support |

**Mitigation strategies:**
1. Extract helper functions where possible (5-10% reduction)
2. Add clear section comments
3. Keep methods focused and well-documented
4. Future: Add language support for split impl blocks

---

**Created by:** Claude Sonnet 4.5
**Date:** February 12, 2026
