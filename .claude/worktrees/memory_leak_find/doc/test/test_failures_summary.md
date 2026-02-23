# Test Failures Summary - 2026-02-06

**Generated:** 2026-02-06 09:19:40
**Total Failing Files:** 355 out of 903 test files
**Success Rate:** 60.7% (548 passing)

## Overview

This report groups all currently failing tests by category/database for systematic analysis and fixing.

## Failures by Category

| Category | Count | Percentage |
|----------|-------|------------|
| **lib** | 169 | 47.6% |
| **other** | 75 | 21.1% |
| **system** | 53 | 14.9% |
| **std** | 15 | 4.2% |
| **app** | 14 | 3.9% |
| **specs** | 13 | 3.7% |
| **integration** | 4 | 1.1% |
| **app_interpreter_async_runtime** | 3 | 0.8% |
| **app_interpreter_collections** | 2 | 0.6% |
| **app_interpreter_lazy** | 2 | 0.6% |
| **app_interpreter_memory** | 2 | 0.6% |
| **app_interpreter_core** | 1 | 0.3% |
| **app_interpreter_helpers** | 1 | 0.3% |
| **app_interpreter_perf** | 1 | 0.3% |

## Failures by Error Type

| Error Type | Count | Description |
|-----------|-------|-------------|
| **runtime_error** | 315 | Runtime execution errors (88.7%) |
| **semantic_error** | 24 | Semantic analysis failures (6.8%) |
| **parse_error** | 11 | Parser syntax errors (3.1%) |
| **compile_error** | 5 | Compilation failures (1.4%) |

## Top Problem Areas

### 1. Library Tests (169 failures - 47.6%)
The largest category of failures is in library tests (`test/lib/`). Key subcategories:
- Standard library features
- Compiler infrastructure
- Type system tests
- Integration tests

**Common Issues:**
- Missing or unimplemented runtime functions
- Static method calls not supported
- Deprecated syntax (`from ... import`)

### 2. Other/Uncategorized (75 failures - 21.1%)
Tests that don't fit standard categories, including:
- Remote debugging features
- QEMU integration
- DAP (Debug Adapter Protocol)
- Build system tests

### 3. System Tests (53 failures - 14.9%)
Core system functionality tests:
- Feature specifications
- Type checker tests
- Collections (BTree, HashMap)
- GPU/CUDA integration

### 4. Application Tests (26 failures total)
- Main app category: 14 failures
- Interpreter subcategories: 12 failures
  - async_runtime: 3
  - collections: 2
  - lazy: 2
  - memory: 2
  - others: 3

## Critical Issues to Address

### Parse Errors (11 files)
These indicate fundamental syntax support issues:
- `Assert` keyword not recognized
- `Indent` token unexpected
- Pattern matching syntax issues
- `Mixin` keyword in patterns

**Example:**
```
test/app/build/link_bins_spec.spl
Error: parse error: Unexpected token: expected expression, found Assert
```

### Semantic Errors (24 files)
Type system and name resolution issues:
- Type mismatches (dict to int conversions)
- Variable/function not found
- Unsupported path calls (static methods)

**Common Pattern:**
```
Error: semantic: type mismatch: cannot convert dict to int
Error: semantic: unsupported path call: ["Type", "method"]
Error: semantic: variable `from` not found
```

### Runtime Errors (315 files - 88.7%)
The majority of failures occur at runtime. Many show no error message, indicating:
- Test framework issues
- Missing dependencies
- Unimplemented features
- Static method support (being addressed)

## Recommended Fix Priority

### Phase 1: Critical Infrastructure (Blocking many tests)
1. **Static method support** - Already being addressed via desugaring (see memory notes)
2. **Deprecated syntax migration** - `from ... import` → `use`
3. **Parse errors** - Fix Assert, Indent, Mixin token issues

### Phase 2: Type System Issues
1. Fix dict-to-int type conversion errors (appears in 4+ files)
2. Resolve "unsupported path call" errors
3. Fix variable/function resolution failures

### Phase 3: Runtime Stability
1. Investigate tests with no error messages (silent failures)
2. Fix missing runtime functions
3. Improve error reporting in test framework

### Phase 4: Feature Completeness
1. Library tests (once infrastructure fixed)
2. System tests (advanced features)
3. Integration tests (end-to-end scenarios)

## Database Reference

Full failure details are stored in SDN format:
- **Database:** `doc/test/test_failures_grouped.sdn`
- **Tables:** `summary`, `failures`, `error_types`

Query examples:
```bash
# Get all parse errors
grep "parse_error" doc/test/test_failures_grouped.sdn

# Get app category failures
grep "^    [0-9]*, app," doc/test/test_failures_grouped.sdn

# Count by error type
grep "runtime_error\|semantic_error\|parse_error" doc/test/test_failures_grouped.sdn | wc -l
```

## Next Steps

1. **Review:** `doc/test/test_failures_grouped.sdn` for complete failure list
2. **Fix:** Start with Phase 1 critical infrastructure issues
3. **Re-test:** Run `bin/simple test` after fixes
4. **Update:** Regenerate this report to track progress

## Notes

- Test timeout bug was fixed (see `doc/report/test_timeout_bug_fix_2026-02-06.md`)
- Static method support is in progress (desugaring approach)
- 122 stale test runs were cleaned up
- Current test database may have parsing issues (separate from test failures)

---

**Generated by:** Test failure analysis script
**Command:** `bin/simple test 2>&1 | python3 analyze_failures.py`
