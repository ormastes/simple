# 100% Branch Coverage Implementation - Status Report

**Generated:** 2026-02-03
**Goal:** Achieve 100% branch coverage on Simple standard library (`src/std/`)
**Methodology:** Proven formatter approach (78 tests → 85% coverage)

---

## Executive Summary

**Status:** Phase 1 (Memory Subsystem) - Week 1 Started
- **Current Coverage:** ~6% estimated (220/3,500 branches)
- **Target:** 100% on Priority 0/1 modules, 95%+ overall
- **Timeline:** 12 weeks (480 hours estimated)
- **Tests to Write:** ~2,500 new tests

---

##Phase Plan

| Phase | Modules | Weeks | Tests | Status |
|-------|---------|-------|-------|--------|
| **Phase 1: Memory** | allocator, gc, runtime_value, rc | 3 | 250-300 | ✅ **STARTED** |
| Phase 2: I/O | fs, net, binary_io | 2 | 290-320 | Pending |
| Phase 3: Concurrency | async, concurrent, atomic | 2 | 195-220 | Pending |
| Phase 4: Collections | map, set, table, tensor, hash | 2 | 300-330 | Pending |
| Phase 5: Utilities | json, path, di, log, time | 2 | 191-215 | Pending |
| Phase 6: Advanced | testing, math, tooling | 1 | 470 | Pending |

---

## Current Week: Week 1 - Allocator Module

### Day 1-2: Baseline & Audit (IN PROGRESS)

**Tasks:**
- [x] Understand coverage infrastructure (SIMPLE_COVERAGE env var)
- [x] Identify test files: `test/lib/std/unit/allocator_spec.spl` (455 lines, 55 tests)
- [x] Identify source: `src/std/allocator.spl` (601 LOC)
- [ ] Run targeted coverage analysis on allocator
- [ ] Map existing 55 tests to source branches
- [ ] Identify coverage gaps

**Findings:**
- Coverage system uses `SIMPLE_COVERAGE=1` environment variable
- Data collected in Rust runtime (`rust/runtime/src/coverage.rs`)
- Reports available in SDN, JSON, HTML, LCOV formats
- Coverage API: `std.tooling.coverage` module
- Existing test suite: 55 tests across 4 allocators (System, Arena, Pool, Slab)

### Day 2-3: First 10 Tests

**Target Branches (ArenaAllocator):**
1. Alignment edge case: offset not aligned, needs padding
2. Alignment edge case: offset already aligned
3. Capacity check: exact fit (remaining == size)
4. Capacity check: overflow prevented
5. Reset with active allocations
6. Allocate with zero alignment (error path)
7. Allocate with non-power-of-2 alignment (error path)
8. Multiple consecutive allocations fill arena exactly
9. Allocation after reset uses same memory
10. Remaining capacity calculation with padding

**Methodology:**
```simple
# Helper function per code path
fn allocate_with_misaligned_offset(arena: ArenaAllocator) -> bool:
    arena.allocate(10, 8)  # Offset now at 10
    val ptr = arena.allocate(10, 16)  # Needs alignment padding
    ptr.?

# Explicit test per branch
describe "ArenaAllocator.allocate":
    context "when offset needs alignment padding":
        it "should add padding and allocate":
            val arena = ArenaAllocator(capacity: 256)
            val result = allocate_with_misaligned_offset(arena)
            expect result to_be_true
```

### Day 4-7: Complete Allocator (40 tests total)

**Coverage targets:**
- ArenaAllocator: 80 branches
- PoolAllocator: 50 branches
- SlabAllocator: 60 branches
- SystemAllocator: 20 branches

---

## Coverage Infrastructure

### Enabling Coverage

```bash
# Method 1: Environment variable
export SIMPLE_COVERAGE=1
simple test test/lib/std/unit/allocator_spec.spl

# Method 2: Via API
import std.tooling.coverage as cov
if cov.is_coverage_enabled():
    val report = cov.get_coverage_sdn()
    cov.save_coverage_data(quiet: false)
```

### Verification Workflow

```bash
# 1. Run tests with coverage
SIMPLE_COVERAGE=1 simple test test/lib/std/unit/allocator_spec.spl

# 2. Check coverage was collected
simple spl-coverage status

# 3. Save coverage report
simple spl-coverage dump > .coverage/allocator_baseline.sdn

# 4. Analyze gaps (manual inspection of .sdn file)

# 5. Write new tests targeting uncovered branches

# 6. Re-run and verify improvement
SIMPLE_COVERAGE=1 simple test test/lib/std/unit/allocator_spec.spl
simple spl-coverage dump > .coverage/allocator_iteration_1.sdn
```

---

## Test Writing Standards

### Template (from `.claude/templates/sspec_template.spl`)

```simple
# Feature: Memory Allocation
# Test coverage for src/std/allocator.spl

use std.allocator.*
use std.test.sspec.*

describe "ComponentName":
    context "when specific condition":
        it "should have expected behavior":
            # Arrange
            val allocator = ArenaAllocator(capacity: 1024)

            # Act
            val result = allocator.allocate(128, 8)

            # Assert
            expect result.? to_be_true
            expect allocator.remaining() to_equal (1024 - 128)
```

### Principles

1. **One test per branch** - Each if/elif/else/match arm gets a test
2. **Helper functions** - Extract path setup into reusable functions
3. **Boundary conditions** - Test 0, 1, max, max+1 values
4. **Error paths** - Explicitly test None/Error returns
5. **Verify incrementally** - Run coverage after each batch of 10 tests

---

## Metrics Tracking

### Baseline (2026-02-03)

| Module | LOC | Est. Branches | Tests | Coverage |
|--------|-----|---------------|-------|----------|
| allocator.spl | 601 | ~80 | 55 | TBD |
| gc.spl | 648 | ~120 | 0 | 0% |
| runtime_value.spl | 575 | ~90 | 0 | 0% |
| rc.spl | 360 | ~70 | 0 | 0% |

### Week 1 Target

| Module | Tests | Coverage |
|--------|-------|----------|
| allocator.spl | 95 (+40) | 100% |

---

## Key Files

| File | Purpose |
|------|---------|
| `test/lib/std/unit/allocator_spec.spl` | Existing allocator tests (455 lines, 55 tests) |
| `src/std/allocator.spl` | Allocator implementations (601 LOC, ~80 branches) |
| `.coverage/coverage.sdn` | Coverage data in SDN format |
| `rust/runtime/src/coverage.rs` | Coverage collection runtime |
| `rust/lib/std/src/tooling/coverage.spl` | Coverage API |
| `src/app/spl_coverage/main.spl` | Coverage CLI tool |

---

## Next Actions

1. **TODAY:** Complete baseline coverage measurement
   - Run: `SIMPLE_COVERAGE=1 simple test test/lib/std/unit/allocator_spec.spl`
   - Save: `simple spl-coverage dump > doc/coverage/baseline_allocator.sdn`
   - Analyze: Identify top 10 uncovered branches

2. **Tomorrow:** Write first 10 tests
   - Focus on ArenaAllocator alignment and capacity edges
   - Verify coverage increases
   - Establish velocity (tests per hour)

3. **This Week:** Complete allocator to 100%
   - Add 40 total new tests
   - Cover all 4 allocator types
   - Document patterns for next modules

---

## References

- **Plan Document:** (this was created from the plan provided by user)
- **Methodology:** Proven formatter approach (doc/report/coverage_session_2026-02-03.md)
- **Coverage Architecture:** doc/design/coverage_architecture.md
- **SSpec Template:** .claude/templates/sspec_template.spl
- **Coding Standards:** /coding skill

---

**Last Updated:** 2026-02-03 06:45 UTC
**Next Review:** 2026-02-04 (after first 10 tests written)
