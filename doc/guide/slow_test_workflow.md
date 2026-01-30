# Slow Test Development Workflow

**Last Updated:** 2026-01-30

## Overview

7 test files have been marked with `# @slow` tags totaling ~28 seconds of runtime (16.5% of total test time). These can be excluded during quick development cycles for faster iteration.

---

## Slow Test Files

| File | Runtime | Tests | Note |
|------|---------|-------|------|
| test/app/test_analysis_spec.spl | 16.6s | 56 | CLI analysis tool |
| test/lib/std/unit/mcp/symbol_table_spec.spl | 4.0s | 27 | MCP symbol tables |
| test/lib/std/unit/mcp/mcp_spec.spl | 2.0s | ? | MCP protocol types |
| test/lib/std/unit/core/regex_spec.spl | 1.6s | ? | Regex engine |
| test/lib/std/unit/mcp/transport_edge_cases_spec.spl | 1.5s | ? | MCP transport |
| test/lib/std/unit/mcp/failure_analysis_spec.spl | 1.4s | ? | MCP failure analysis |
| test/lib/std/unit/mcp/dependencies_spec.spl | 1.4s | ? | MCP dependencies |

**Total:** ~28.4 seconds

---

## Development Workflows

### Quick Development Cycle (Exclude Slow Tests)

**Manual Exclusion:**
```bash
# Run all tests EXCEPT slow ones (manual file exclusion)
./target/debug/simple_old test \
    --exclude test/app/test_analysis_spec.spl \
    --exclude test/lib/std/unit/mcp/ \
    --exclude test/lib/std/unit/core/regex_spec.spl
```

**Expected Runtime:** ~144 seconds (vs 172s full suite)
**Savings:** 28 seconds (16% faster)

### Full Test Suite (Before Commit)

```bash
# Run ALL tests including slow ones
./target/debug/simple_old test
```

**Runtime:** ~172 seconds
**Use When:** Before commits, PR submissions, CI/CD

### Run Only Slow Tests

```bash
# Verify slow tests still pass
./target/debug/simple_old test test/app/test_analysis_spec.spl
./target/debug/simple_old test test/lib/std/unit/mcp/
./target/debug/simple_old test test/lib/std/unit/core/regex_spec.spl
```

**Runtime:** ~28 seconds
**Use When:** After changes to MCP, CLI tools, or regex

---

## Tag-Based Filtering (Future)

All slow test files have been marked with `# @slow` comments for future tag-based filtering:

```simple
# @slow
# Performance note: ~X seconds runtime. Exclude for quick dev cycles.
```

**When tag filtering is fully implemented:**
```bash
# Run tests excluding slow tag
./target/debug/simple_old test --exclude-tag slow

# Run only slow tests
./target/debug/simple_old test --tag slow
```

**Note:** Tag-based filtering may require test runner enhancements.

---

## Why These Tests Are Slow

### Root Causes

1. **Interpreter Overhead** (Primary)
   - Tests run in interpreter mode (~100-300ms overhead per test)
   - test_analysis_spec.spl: 56 tests * 297ms/test = 16.6s

2. **Complex Operations** (Secondary)
   - MCP symbol table operations (hash map lookups, graph traversal)
   - Regex compilation and matching
   - SDN file I/O

### Future Optimizations

1. **Compile Hot Paths** - Compile frequently-run test suites
2. **Add Test Caching** - Share expensive setup across tests
3. **Optimize Interpreter** - JIT for hot loops, better dispatch

**See:** `/doc/report/test_performance_profile_2026-01-30.md`

---

## Hanging Test

**File:** `test/system/features/async_features/async_features_spec.spl`
**Status:** Times out at 120 seconds (70% of runtime)
**Impact:** Critical - wastes majority of test time

**Current Workaround:**
```bash
# Exclude hanging test
./target/debug/simple_old test --exclude test/system/features/async_features/
```

**Runtime with workaround:** ~52 seconds (70% faster)

**Fix Status:** In progress - see Task #6

---

## Recommended Workflow

**During Active Development:**
```bash
# Fast iteration (52s runtime)
./target/debug/simple_old test \
    --exclude test/app/test_analysis_spec.spl \
    --exclude test/lib/std/unit/mcp/ \
    --exclude test/lib/std/unit/core/regex_spec.spl \
    --exclude test/system/features/async_features/
```

**Before Committing:**
```bash
# Full suite except hanging test (52s runtime)
./target/debug/simple_old test \
    --exclude test/system/features/async_features/
```

**Full Verification (if needed):**
```bash
# Complete test suite (172s runtime)
./target/debug/simple_old test
```

---

## Metrics

| Scenario | Runtime | Tests | Pass Rate |
|----------|---------|-------|-----------|
| **Full suite** | 172.5s | 7,810 | 88.2% |
| **Exclude slow** | 144s | ~7,700 | ~88% |
| **Exclude slow + hanging** | 52s | ~7,660 | ~88% |
| **Quick dev cycle** | **52s** | **~7,660** | **~88%** |

**Recommended:** Use quick dev cycle (52s) for fast iteration, full suite before commits.

---

## Files Modified

All files with `# @slow` tags added:

1. `/test/app/test_analysis_spec.spl`
2. `/test/lib/std/unit/mcp/symbol_table_spec.spl`
3. `/test/lib/std/unit/mcp/mcp_spec.spl`
4. `/test/lib/std/unit/core/regex_spec.spl`
5. `/test/lib/std/unit/mcp/transport_edge_cases_spec.spl`
6. `/test/lib/std/unit/mcp/failure_analysis_spec.spl`
7. `/test/lib/std/unit/mcp/dependencies_spec.spl`

---

**Next Steps:** Debug and fix hanging async test (see Task #6)
