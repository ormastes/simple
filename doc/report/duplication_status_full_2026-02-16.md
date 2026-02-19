# Complete Duplication Status Analysis

**Date:** 2026-02-16
**Scope:** Full codebase duplication analysis after Phase 1-4 consolidation

## Executive Summary

After eliminating 1,787 lines through semantic deduplication (Phases 1-4), the codebase contains **~31,700 lines** of intentional duplication across several categories. The largest category is the compiler/ vs compiler_core_legacy/ split (~30,000 lines), which serves a critical bootstrap purpose.

## Duplication Categories

### 1. Compiler Bootstrap Split (compiler/ vs compiler_core_legacy/)

**Status:** 🟡 ARCHITECTURAL (Partially Consolidatable)

#### Statistics
- **compiler_core_legacy/**: 441 files, 97,057 lines
- **compiler/**: 436 files, 140,315 lines
- **Shared filenames**: 398 files (90%)
- **Unique to compiler_core_legacy**: 43 files
- **Unique to compiler**: 38 files
- **Files that differ**: ~390 (98% of shared files)

#### Purpose: Bootstrap Chain
```
seed.cpp → compiler_core_legacy/ → compiler/ → production
```

1. **Phase 0 (seed.cpp):** C++ seed compiler compiles compiler_core_legacy/
2. **Phase 1 (compiler_core_legacy/):** Produces simple-v1 compiler
3. **Phase 2 (compiler/):** simple-v1 compiles full compiler
4. **Phase 3 (production):** Full-featured compiler

#### Key Differences

**compiler_core_legacy/ (Seed-Compilable)**
```simple
# Manual Option handling (no ? syntax)
struct FunctionDef:
    has_return_type: bool
    return_type: text
    has_specialization_of: bool
    specialization_of: text
```

**compiler/ (Full-Featured)**
```simple
# Modern Option types
struct FunctionDef:
    return_type: text?
    specialization_of: text?
```

#### What's Duplicated
- **Core AST structures** (with different Option handling)
- **Parser logic** (simplified in core, full-featured in compiler)
- **Type system** (basic in core, advanced in compiler)
- **Code generation** (minimal in core, optimized in compiler)
- **Backend selection** (limited in core, full in compiler)

#### Consolidation Potential: MEDIUM (~10,000-15,000 lines)

**CAN Consolidate:**
- **Pure algorithms** (graph traversal, sorting, searching) - ~3,000 lines
- **String processing utilities** - ~2,000 lines
- **Math/numeric helpers** - ~1,000 lines
- **Data structure operations** (not depending on Option) - ~4,000 lines
- **Architecture-independent logic** - ~5,000 lines

**MUST Keep Duplicated:**
- **AST definitions** (Option vs manual handling) - ~8,000 lines
- **Type representations** (different complexity levels) - ~6,000 lines
- **Parser state management** (different patterns) - ~4,000 lines
- **Semantic analysis** (different feature sets) - ~7,000 lines

#### Recommended Approach: Shared Core + Extensions

**Phase A: Extract Shared Algorithms**
```
src/
  compiler_shared/     # New: 15,000 lines
    algorithms/        # Graph, sort, search
    utilities/         # String, math, collections
    patterns/          # Common patterns

  compiler_core_legacy/       # Keep: 82,000 lines (reduced from 97K)
    ast_core.spl       # Seed-compatible AST
    parser_core.spl    # Basic parser
    (imports from compiler_shared/)

  compiler/            # Keep: 125,000 lines (reduced from 140K)
    ast_full.spl       # Full AST with Options
    parser_full.spl    # Full-featured parser
    (imports from compiler_shared/)
```

**Estimated savings:** 15,000 lines
**Risk:** MEDIUM (requires careful bootstrap testing)
**Benefit:** Shared bug fixes, easier maintenance

---

### 2. Zero-Import Lite Files

**Status:** 🔴 CONSTRAINED (Cannot Consolidate)

#### Files
- `src/app/mcp/main_lite.spl` (150 lines)
- `src/app/mcp/fileio_lite.spl` (120 lines)
- `src/app/mcp_jj/main_lite.spl` (130 lines)

**Total:** ~400 lines

#### Duplicated Elements
- JSON helpers (Q, LB, RB, escape_json, js, jp) - 80 lines each
- Protocol I/O (read_stdin_message, write_stdout_message) - 30 lines each
- Basic response builders - 40 lines each

#### Why Kept
- **Startup time:** Must start in <50ms
- **No dependencies:** Zero imports = zero module loading overhead
- **Embedded use:** Designed for resource-constrained environments
- **Critical path:** Fast tools for development workflow

#### Recommendation: KEEP AS-IS
Zero-import constraint is a valid architectural decision. The duplication cost (400 lines) is acceptable for the performance benefit.

---

### 3. Lazy Startup Optimization

**Status:** 🟡 PERFORMANCE (Should Not Consolidate)

#### File
- `src/app/mcp/main_lazy.spl` (~200 lines)

#### Duplicated Elements
- JSON helpers (inlined) - 80 lines
- Protocol I/O (inlined) - 30 lines
- Basic tool schemas (inlined) - 90 lines

#### Why Kept
- **Fast startup:** ~100ms with lazy handler loading
- **Lazy dispatch:** Handlers loaded on-demand via subprocess
- **Trade-off:** Duplication for startup speed

#### Recommendation: KEEP AS-IS
Lazy loading architecture requires minimal dependencies. The 200-line duplication is acceptable for 10x startup improvement.

---

### 4. Lexer Variants

**Status:** 🟡 ARCHITECTURAL (Should Not Consolidate)

#### Files
- `src/compiler_core_legacy/lexer.spl` (module-state based) - ~300 lines
- `src/compiler_core_legacy/lexer_struct.spl` (struct-state based) - ~300 lines

**Total duplication:** ~600 lines

#### Why Duplicated
- **Module-state lexer:** Used by runtime interpreter (fast, global state)
- **Struct-state lexer:** Used by compiler (reentrant, thread-safe)
- **Seed compatibility:** Both needed for bootstrap process

#### Shared Logic Extracted
- Character classification → `src/compiler_core_legacy/lexer_chars.spl` (Phase 3) ✅

#### Remaining Duplication
- Tokenization loops (different state management)
- Token accumulation (different patterns)
- Error handling (different contexts)

#### Recommendation: KEEP AS-IS
The architectural difference (module vs struct state) makes full consolidation impractical. Already extracted shared character functions.

---

### 5. Eval Hashmap Boilerplate

**Status:** 🔴 LANGUAGE LIMITATION (Cannot Consolidate)

#### Location
- `src/compiler_core_legacy/interpreter/eval.spl` (11 instances)

**Total:** ~300 lines

#### Pattern
```simple
# Repeated 11 times for different value types
var symbol_table: {text: Value} = {}

fn symbol_set(name: text, value: Value):
    symbol_table[name] = value

fn symbol_get(name: text) -> Value?:
    if symbol_table.contains(name):
        return symbol_table[name]
    nil
```

#### Why Duplicated
- **No generic hashmap:** Language doesn't support `HashMap<K, V>` yet
- **Type-specific:** Each hashmap needs custom wrapper for different value types
- **Seed-compilable:** Can't use advanced type features

#### Recommendation: LANGUAGE FEATURE NEEDED
Once generic collections are available, this can be consolidated to ~30 lines with `HashMap<text, T>`.

**Blocked on:** Generic type system implementation

---

### 6. Expression vs Statement Duplication

**Status:** 🟢 SEMANTIC (Should Not Consolidate)

#### Location
- `src/compiler_core_legacy/interpreter/eval.spl`

**Total:** ~200 lines

#### Why Duplicated
- **Expressions:** Return values, can be composed
- **Statements:** Side effects only, no return value
- **Semantic difference:** Different evaluation contexts

#### Example
```simple
fn eval_expression(expr: Expr) -> Value:
    match expr:
        BinaryOp: eval_binary(expr)
        FunctionCall: eval_call(expr)
        # ... returns Value

fn eval_statement(stmt: Stmt) -> ():
    match stmt:
        Assignment: eval_assign(stmt)
        Return: eval_return(stmt)
        # ... returns unit
```

#### Recommendation: KEEP AS-IS
Semantic difference justifies separate implementations. Attempting to unify would add complexity.

---

### 7. Future Consolidation Opportunities

**Status:** 🟢 IDENTIFIED (Not in Original Scope)

#### Candidates

**A. File Discovery (~200 lines)**
- `find_spl_files()` duplicated in 10+ tools
- Pattern: recursively find `.spl` files in directory
- **Consolidation:** Extract to `src/std/file_discovery.spl`
- **Risk:** LOW
- **Benefit:** 180 lines saved

**B. Duration Formatting (~200 lines)**
- `format_duration_ms()` duplicated in 9 files
- Pattern: convert milliseconds to "1.23s" or "450ms"
- **Consolidation:** Extract to `src/std/format_utils.spl`
- **Risk:** LOW
- **Benefit:** 180 lines saved

**C. MCP Initialize Response (~150 lines)**
- Similar patterns across 4 MCP servers
- Pattern: build capabilities JSON, server info
- **Consolidation:** Extract template to `src/mcp_lib/init_response.spl`
- **Risk:** MEDIUM (server-specific capabilities)
- **Benefit:** 120 lines saved

**D. Handler Dispatch (~100 lines)**
- Tool routing logic duplicated in 3 servers
- Pattern: method name → handler function mapping
- **Consolidation:** Extract to `src/mcp_lib/dispatch.spl`
- **Risk:** MEDIUM (different tool sets)
- **Benefit:** 70 lines saved

**Total potential:** ~550 lines

---

## Summary Table

| Category | Lines | Status | Consolidatable | Action |
|----------|-------|--------|----------------|--------|
| Compiler bootstrap | 30,000 | 🟡 Architectural | 15,000 (50%) | Phase A: Extract shared algorithms |
| Lite files | 400 | 🔴 Constrained | 0 | Keep (performance) |
| Lazy startup | 200 | 🟡 Performance | 0 | Keep (optimization) |
| Lexer variants | 600 | 🟡 Architectural | 0 | Keep (already extracted chars) |
| Hashmap boilerplate | 300 | 🔴 Language | 0 | Wait for generics |
| Expr vs Stmt | 200 | 🟢 Semantic | 0 | Keep (semantic difference) |
| **Subtotal** | **31,700** | | **15,000** | |
| Future opportunities | 550 | 🟢 Identified | 550 (100%) | Phase 5: Extract utilities |
| **GRAND TOTAL** | **32,250** | | **15,550** | |

## Recommendations

### Immediate (Do Now)
✅ **Nothing** - Phases 1-4 complete, constraints respected

### Short-Term (Next Quarter)
1. **Phase 5:** Extract future opportunities (~550 lines, LOW risk)
   - File discovery utilities
   - Duration formatting
   - LOW risk, HIGH benefit

### Mid-Term (Next 6 Months)
2. **Phase A:** Extract compiler shared algorithms (~15,000 lines, MEDIUM risk)
   - Create `src/compiler_shared/` module
   - Extract pure algorithms and utilities
   - Requires extensive bootstrap testing
   - MEDIUM risk, VERY HIGH benefit

### Long-Term (When Language Ready)
3. **Generic Collections:** Once language supports generics, consolidate hashmap boilerplate (~300 lines)

### Never (Keep As-Is)
- Lite files (zero-import constraint)
- Lazy startup files (performance optimization)
- Lexer variants (architectural difference)
- Expr vs Stmt (semantic difference)

## Metrics

### Current State (Post Phase 1-4)
- **Eliminated:** 1,787 lines
- **Remaining intentional:** 31,700 lines
- **Total codebase:** ~623,000 lines
- **Duplication rate:** 5.1%

### Potential After All Phases
- **Phase 5 (future opportunities):** -550 lines
- **Phase A (compiler shared):** -15,000 lines
- **Total potential:** -17,337 lines
- **Final duplication:** 14,363 lines (2.3%)
- **Final constrained duplication:** 700 lines (0.1%)

### Acceptable Duplication Target
**2-3%** is considered acceptable for systems with:
- Bootstrap requirements
- Performance constraints
- Zero-dependency requirements
- Architectural variants

**Conclusion:** Current 5.1% is acceptable. With Phase 5+A, reaching 2.3% would be excellent.

---

## Historical Context

### Phases 1-4 (Completed 2026-02-16)
- Phase 1: Stdlib consolidation (1,157 lines)
- Phase 2: Cross-cutting utilities (510 lines)
- Phase 3: Core compiler chars (52 lines)
- Phase 4: MCP protocol (68 lines)
- **Total: 1,787 lines eliminated**

### Discovered During Analysis
- Compiler bootstrap split is larger than estimated (30,000 vs 10,000)
- 50% of compiler code could potentially be shared
- Future opportunities identified (550 lines)

---

## Related Documents
- Phases 1-4 Summary: `doc/report/semantic_deduplication_complete_2026-02-16.md`
- Phase 4 Report: `doc/report/phase4_mcp_protocol_consolidation_2026-02-16.md`
- Original Plan: `.claude/plans/calm-nibbling-octopus.md`
- Architecture: `doc/architecture/file_class_structure.md`
