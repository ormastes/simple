# Implementable Skipped Tests Analysis - 2026-01-21

## Executive Summary

**Total Skipped Tests:** 1,004
**Files with Skips:** 112
**Immediately Implementable:** ~69 tests across 5 core modules

## Priority 1: Fully Implemented Modules (Need Tests Only)

### 1. Math Module ⭐⭐⭐
**Status:** ✅ FULLY IMPLEMENTED
**Implementation:** `src/lib/std/src/compiler_core/math.spl` (308 lines, 44 exports)
**Skipped Tests:** 29
**Effort:** Low (tests only, ~2 hours)

**Available Functions:**
- Constants: `PI()`, `E()`, `TAU()`, `INF()`, `NAN()`
- Basic: `abs()`, `abs_int()`, `sign()`, `floor()`, `ceil()`, `round()`, `trunc()`
- Power/Roots: `pow()`, `sqrt()`, `cbrt()`
- Exponential: `exp()`, `log()`, `log10()`, `log2()`
- Trigonometry: `sin()`, `cos()`, `tan()`, `asin()`, `acos()`, `atan()`, `atan2()`
- Hyperbolic: `sinh()`, `cosh()`, `tanh()`
- Utility: `min()`, `max()`, `min_int()`, `max_int()`, `clamp()`, `clamp_int()`
- Conversion: `radians()`, `degrees()`
- Integer Math: `factorial()`, `gcd()`, `lcm()`
- Float Checks: `is_close()`, `is_nan()`, `is_inf()`, `is_finite()`

**Test Categories:**
- Constants (3 tests) - PI, E, TAU
- Basic operations (6 tests) - abs, sign, floor, ceil, round
- Exponential and roots (2 tests) - sqrt, exp
- Trigonometry (5 tests) - sin, cos, tan, radians, degrees
- Min/Max (4 tests) - min/max for floats and ints
- Clamping (2 tests) - clamp for floats and ints
- Integer math (3 tests) - factorial, gcd, lcm
- Float comparisons (4 tests) - is_close, is_nan, is_inf, is_finite

### 2. Random Module ⭐⭐
**Status:** ✅ FULLY IMPLEMENTED
**Implementation:** `src/lib/std/src/compiler_core/random.spl` (271 lines, 16 exports)
**Skipped Tests:** 12
**Effort:** Low (tests only, ~1.5 hours)

**Available Functions:**
- Seeding: `seed()`, `getstate()`, `setstate()`, `seed_bytes()`
- Integers: `randint()`, `randrange()`
- Floats: `random()`, `uniform()`
- Sequences: `choice()`, `choices()`, `shuffle()`, `sample()`
- Utilities: `randbytes()`, `randbool()`
- Distributions: `gauss()`, `expovariate()`

**Test Categories:**
- Seeding (2 tests) - set seed, get/set state
- Random integers (2 tests) - randint, uniform integer
- Random floats (2 tests) - random 0-1, uniform float range
- Sequences (4 tests) - choice, choices, shuffle, sample
- Distributions (2 tests) - normal, exponential

### 3. Synchronization Module ⭐
**Status:** ✅ FULLY IMPLEMENTED
**Implementation:** `src/lib/std/src/compiler_core/synchronization.spl` (324 lines)
**Skipped Tests:** 4
**Effort:** Low (tests only, ~1 hour)

**Available Classes:**
- `Atomic` - Atomic operations with `load()`, `store()`, `swap()`, `compare_and_swap()`, `fetch_add()`, `fetch_sub()`
- `Mutex` - Mutual exclusion locks with `lock()`, `unlock()`
- `RwLock` - Reader-writer locks with `read()`, `write()`, `set()`
- `Semaphore` - Counting semaphore with `acquire()`, `release()`, context manager support

**Test Categories:**
- Atomic (4+ operations) - load, store, swap, fetch_add, fetch_sub, CAS
- Mutex (2+ tests) - lock/unlock, mutual exclusion
- RwLock (2+ tests) - read, write, multiple readers
- Semaphore (2+ tests) - acquire/release, counting

**Note:** Previously had test implementation challenges (accessing internal state). Need strategy for testing without exposing internals.

### 4. Regex Module ✅
**Status:** ✅ FULLY IMPLEMENTED
**Implementation:** `src/lib/std/src/compiler_core/regex.spl` (1400 lines, 25 exports)
**Skipped Tests:** 1 (overlapping matches)
**Effort:** Very Low (~15 minutes)

**Remaining Skip:**
- "handle overlapping matches - needs clarification on behavior"

**Action:** Define expected behavior for overlapping matches, then implement test.

## Priority 2: Partially Implemented Modules

### 5. Decorators Module ⭐
**Status:** 🟡 PARTIAL
**Implementation:** `src/lib/std/src/compiler_core/decorators.spl` (261 lines, partial)
**Skipped Tests:** 10
**Effort:** Medium (~3-4 hours - complete implementation + tests)

**Implemented:**
- `@cached` - CachedFunction class with cache, hits, misses tracking

**Missing:**
- `@logged` - Logging decorator
- `@deprecated` - Deprecation warnings
- `@timeout` - Execution timeout
- Decorator composition mechanics

**Test Categories:**
- @cached (2 tests) - caches results, different arguments
- @logged (2 tests) - logs calls, includes return value
- @deprecated (2 tests) - shows warning, replacement message
- @timeout (2 tests) - raises error on timeout, returns on completion
- Composition (2 tests) - multiple decorators, correct order

### 6. Context Module
**Status:** 🟡 PARTIAL
**Implementation:** `src/lib/std/src/compiler_core/context.spl` (396 lines)
**Skipped Tests:** 7
**Effort:** Medium (~2-3 hours)

### 7. DSL Module
**Status:** 🟡 PARTIAL
**Implementation:** `src/lib/std/src/compiler_core/dsl.spl` (691 lines)
**Skipped Tests:** 6
**Effort:** Medium (~2-3 hours)

## Priority 3: Not Implemented (Placeholder Tests)

### Major Feature Areas:
- **Macros System** (~200 skips, 9 files) - Not implemented
- **Tree-sitter Integration** (~180 skips, 14 files) - Not implemented
- **Game Engine** (~150 skips, 12 files) - Not implemented
- **ML/PyTorch** (~130 skips, 13 files) - Partially implemented
- **Physics Engine** (~80 skips, 6 files) - Not implemented
- **LSP/DAP** (~100 skips, 10 files) - Partially implemented
- **Property Testing** (~60 skips, 3 files) - Not implemented
- **Snapshot Testing** (~60 skips, 4 files) - Not implemented

## Implementation Roadmap

### Phase 1: Quick Wins (Immediate - ~5 hours)
1. ✅ **Regex overlapping matches** (1 test, 15 min) - Define behavior, implement test
2. **Math module** (29 tests, 2 hours) - All features implemented, just need tests
3. **Random module** (12 tests, 1.5 hours) - All features implemented, just need tests
4. **Synchronization module** (4 tests, 1 hour) - Design test strategy without internal state access

**Total:** 46 tests implemented, ~5 hours effort

### Phase 2: Medium Effort (1-2 days)
1. **Decorators module** (10 tests, 3-4 hours) - Complete @logged, @deprecated, @timeout
2. **Context module** (7 tests, 2-3 hours) - Complete missing features
3. **DSL module** (6 tests, 2-3 hours) - Complete missing features

**Total:** 23 tests implemented, ~8-10 hours effort

### Phase 3: Future Work
Major feature areas requiring significant implementation work (macros, tree-sitter, game engine, etc.)

## Recommended Next Steps

1. **Immediate:**
   - Implement math module tests (29 tests)
   - Implement random module tests (12 tests)

2. **Short-term:**
   - Complete decorators module implementation
   - Design synchronization test strategy

3. **Medium-term:**
   - Complete context and DSL modules
   - Address ML/PyTorch partial implementations

4. **Long-term:**
   - Major feature areas as per roadmap

## Success Metrics

- **Current:** 1,004 skipped tests
- **Phase 1 Target:** 958 skipped tests (-46)
- **Phase 2 Target:** 935 skipped tests (-23 more)
- **Overall Phase 1-2:** -69 skipped tests (~7% reduction)

## Notes

- Most skipped tests (70%) are intentional placeholders for future features
- Focus on modules with complete implementations first (math, random)
- Synchronization tests need careful design due to internal state access issues
- Decorator completion is valuable as it's a user-facing feature
