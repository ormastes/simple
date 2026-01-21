# Implementable Features List - 2026-01-21

## Executive Summary

This document lists all features with ignored tests that can be implemented, organized by implementation status and priority.

**Total Implementable:** 97 features (tests)
- **Immediate (features exist, tests ready):** 42 tests (~3.5 hours)
- **Short-term (minor implementation needed):** 24 tests (~5 hours)
- **Medium-term (significant implementation):** 31 doc-tests (variable effort)

---

## Priority 1: Ready to Enable (Features Fully Implemented)

### 1.1 Math Module ⭐⭐⭐

**Status:** ✅ ALL FUNCTIONS IMPLEMENTED
**Implementation:** `src/lib/std/src/core/math.spl:1` (412 lines, 44 exports)
**Tests:** `test/lib/std/unit/core/math_spec.spl:1` (152 lines, 29 tests)
**Effort:** ~2 hours (remove skip tags, verify tests)

#### Constants (3 features)
| Feature | Function | Test Location | Status |
|---------|----------|--------------|---------|
| PI constant | `PI()` | math_spec.spl:10 | ✅ Impl + Test |
| E constant | `E()` | math_spec.spl:14 | ✅ Impl + Test |
| TAU constant | `TAU()` | math_spec.spl:19 | ✅ Impl + Test |

#### Basic Operations (6 features)
| Feature | Function | Test Location | Status |
|---------|----------|--------------|---------|
| Absolute value (float) | `abs(f32)` | math_spec.spl:25 | ✅ Impl + Test |
| Absolute value (int) | `abs_int(i32)` | math_spec.spl:30 | ✅ Impl + Test |
| Sign function | `sign(f32)` | math_spec.spl:35 | ✅ Impl + Test |
| Floor function | `floor(f32)` | math_spec.spl:40 | ✅ Impl + Test |
| Ceiling function | `ceil(f32)` | math_spec.spl:45 | ✅ Impl + Test |
| Rounding | `round(f32)` | math_spec.spl:50 | ✅ Impl + Test |

#### Exponential & Roots (2 features)
| Feature | Function | Test Location | Status |
|---------|----------|--------------|---------|
| Square root | `sqrt(f32)` | math_spec.spl:56 | ✅ Impl + Test |
| Exponential | `exp(f32)` | math_spec.spl:61 | ✅ Impl + Test |

#### Trigonometry (5 features)
| Feature | Function | Test Location | Status |
|---------|----------|--------------|---------|
| Sine | `sin(f32)` | math_spec.spl:67 | ✅ Impl + Test |
| Cosine | `cos(f32)` | math_spec.spl:71 | ✅ Impl + Test |
| Tangent | `tan(f32)` | math_spec.spl:76 | ✅ Impl + Test |
| Degrees to radians | `radians(f32)` | math_spec.spl:80 | ✅ Impl + Test |
| Radians to degrees | `degrees(f32)` | math_spec.spl:85 | ✅ Impl + Test |

#### Min/Max Operations (4 features)
| Feature | Function | Test Location | Status |
|---------|----------|--------------|---------|
| Min (float) | `min(f32, f32)` | math_spec.spl:91 | ✅ Impl + Test |
| Max (float) | `max(f32, f32)` | math_spec.spl:95 | ✅ Impl + Test |
| Min (int) | `min_int(i32, i32)` | math_spec.spl:99 | ✅ Impl + Test |
| Max (int) | `max_int(i32, i32)` | math_spec.spl:103 | ✅ Impl + Test |

#### Clamping (2 features)
| Feature | Function | Test Location | Status |
|---------|----------|--------------|---------|
| Clamp (float) | `clamp(f32, f32, f32)` | math_spec.spl:108 | ✅ Impl + Test |
| Clamp (int) | `clamp_int(i32, i32, i32)` | math_spec.spl:113 | ✅ Impl + Test |

#### Integer Math (3 features)
| Feature | Function | Test Location | Status |
|---------|----------|--------------|---------|
| Factorial | `factorial(i32)` | math_spec.spl:119 | ✅ Impl + Test |
| GCD | `gcd(i32, i32)` | math_spec.spl:124 | ✅ Impl + Test |
| LCM | `lcm(i32, i32)` | math_spec.spl:129 | ✅ Impl + Test |

#### Float Comparisons (4 features)
| Feature | Function | Test Location | Status |
|---------|----------|--------------|---------|
| Close comparison | `is_close(f32, f32)` | math_spec.spl:134 | ✅ Impl + Test |
| NaN detection | `is_nan(f32)` | math_spec.spl:138 | ✅ Impl + Test |
| Infinity detection | `is_inf(f32)` | math_spec.spl:143 | ✅ Impl + Test |
| Finite detection | `is_finite(f32)` | math_spec.spl:148 | ✅ Impl + Test |

**Action Required:** Remove `skip` tags from all 29 tests in `math_spec.spl`

---

### 1.2 Random Module ⭐⭐

**Status:** ✅ ALL FUNCTIONS IMPLEMENTED
**Implementation:** `src/lib/std/src/core/random.spl:1` (272 lines, 16 exports)
**Tests:** `test/lib/std/unit/core/random_spec.spl:1` (86 lines, 12 tests)
**Effort:** ~1.5 hours (remove skip tags, verify tests)

#### Seeding (2 features)
| Feature | Function | Test Location | Status |
|---------|----------|--------------|---------|
| Set seed | `seed(i32)` | random_spec.spl:9 | ✅ Impl + Test |
| Get/set state | `getstate()`, `setstate()` | random_spec.spl:16 | ✅ Impl + Test |

#### Random Integers (2 features)
| Feature | Function | Test Location | Status |
|---------|----------|--------------|---------|
| Random int in range | `randint(i32, i32)` | random_spec.spl:26 | ✅ Impl + Test |
| Random range with step | `randrange(i32, i32, i32)` | random_spec.spl:32 | ✅ Impl + Test |

#### Random Floats (2 features)
| Feature | Function | Test Location | Status |
|---------|----------|--------------|---------|
| Random 0-1 | `random()` | random_spec.spl:38 | ✅ Impl + Test |
| Uniform in range | `uniform(f32, f32)` | random_spec.spl:44 | ✅ Impl + Test |

#### Sequences (4 features)
| Feature | Function | Test Location | Status |
|---------|----------|--------------|---------|
| Choose element | `choice(List)` | random_spec.spl:51 | ✅ Impl + Test |
| Choose k elements | `choices(List, i32)` | random_spec.spl:57 | ✅ Impl + Test |
| Shuffle list | `shuffle(List)` | random_spec.spl:63 | ✅ Impl + Test |
| Sample without replacement | `sample(List, i32)` | random_spec.spl:69 | ✅ Impl + Test |

#### Distributions (2 features)
| Feature | Function | Test Location | Status |
|---------|----------|--------------|---------|
| Normal distribution | `gauss(f32, f32)` | random_spec.spl:76 | ✅ Impl + Test |
| Exponential distribution | `expovariate(f32)` | random_spec.spl:82 | ✅ Impl + Test |

**Action Required:** Remove `skip` tags from all 12 tests in `random_spec.spl`

---

### 1.3 Regex Module ✅

**Status:** ✅ FULLY IMPLEMENTED
**Implementation:** `src/lib/std/src/core/regex.spl:1` (1400 lines, 25 exports)
**Tests:** `test/lib/std/unit/core/regex_spec.spl:91` (1 skip)
**Effort:** ~15 minutes (define behavior + implement test)

#### Overlapping Matches (1 feature)
| Feature | Function | Test Location | Status |
|---------|----------|--------------|---------|
| Handle overlapping matches | `findall()` behavior | regex_spec.spl:91 | ⚠️ Needs behavior definition |

**Note:** Test says "needs clarification on behavior". Need to:
1. Define expected behavior for overlapping matches (e.g., `"aa"` in `"aaaa"` → `["aa", "aa"]` or `["aa"]`?)
2. Implement test based on chosen behavior

**Action Required:**
1. Review regex engine behavior for overlapping matches
2. Document expected behavior
3. Write test case

---

## Priority 2: Minor Implementation Needed

### 2.1 Rust #[ignore] Tests ✅

**Status:** ✅ FULLY WORKING (just too slow)
**Location:** `test/lib/std/unit/verification/regeneration_spec.spl`
**Count:** 3 tests (2 files marked `#[ignore]`)
**Effort:** 0 hours (no work needed)

#### Lean Regeneration (3 features)
| Feature | Test | Status | Reason |
|---------|------|--------|--------|
| Generate all 15 Lean files | regeneration_spec.spl | ✅ Works | 120+ seconds |
| Include all project paths | regeneration_spec.spl | ✅ Works | 120+ seconds |
| Valid Lean headers | regeneration_spec.spl | ✅ Works | 120+ seconds |

**Note:** Tests are fully implemented and working. Marked `#[ignore]` only because they're slow.

**Action Required:** None (tests already work, ignore is intentional)

---

## Priority 3: Doc-Tests (Rust Documentation Examples)

### 3.1 Compiler Doc-Tests (4 ignored)

**Location:** `src/rust/compiler/`
**Effort:** ~1-2 hours

| File | Test | Line | Status |
|------|------|------|--------|
| `interpreter_extern/common/effect_check.rs` | `with_effect_check` | 27 | 🟡 Needs review |
| `linker/builder_macros.rs` | `impl_linker_builder_methods` | 13 | 🟡 Macro example |
| `linker/builder_macros.rs` | `impl_linker_builder_methods` | 21 | 🟡 Macro example |
| `semantics/truthiness.rs` | `TruthinessRules::is_truthy` | 45 | 🟡 Needs review |

**Action Required:** Review each doc-test, verify API matches implementation, update or mark `no_run` if needed

---

### 3.2 Runtime FFI Doc-Tests (10 ignored)

**Location:** `src/rust/runtime/`
**Effort:** ~2-3 hours

#### Concurrent Data Structures (4 tests)
| File | Test | Line | Status |
|------|------|------|--------|
| `concurrent/map.rs` | `ConcurrentMap` | 55 | 🟡 Example |
| `concurrent/mod.rs` | `concurrent` | 31 | 🟡 Example |
| `concurrent/queue.rs` | `ConcurrentQueue` | 28 | 🟡 Example |
| `concurrent/stack.rs` | `ConcurrentStack` | 31 | 🟡 Example |

#### FFI Examples (5 tests)
| File | Test | Line | Status |
|------|------|------|--------|
| `value/ffi/io_capture.rs` | io_capture | 16 | 🟡 FFI example |
| `value/ffi/io_capture.rs` | io_capture | 30 | 🟡 FFI example |
| `value/ffi/io_print.rs` | io_print | 16 | 🟡 FFI example |
| `value/ffi/math.rs` | math | 17 | 🟡 FFI example |
| `value/ffi/time.rs` | time | 22 | 🟡 FFI example |

#### Other (1 test)
| File | Test | Line | Status |
|------|------|------|--------|
| `cuda_runtime.rs` | cuda_runtime | 30 | 🟡 CUDA example |

**Action Required:** Similar to previous doc-test fixes:
1. Read actual source code
2. Verify API matches examples
3. Make examples runnable or mark `no_run` appropriately

---

### 3.3 Infrastructure Doc-Tests (17 ignored)

**Location:** Various crates
**Effort:** ~3-4 hours

#### Database (1 test)
| File | Test | Line | Status |
|------|------|------|--------|
| `db/src/lib.rs` | db example | 21 | 🟡 Needs review |

#### Embedded/GPU/Loader (5 tests)
| File | Test | Line | Status |
|------|------|------|--------|
| `embedded/src/lib.rs` | embedded | 22 | 🟡 Platform example |
| `gpu/src/lib.rs` | gpu | 23 | 🟡 GPU example |
| `loader/src/lib.rs` | loader | 16 | 🟡 Module loading |
| `loader/src/lib.rs` | loader | 22 | 🟡 Module loading |
| `wasm-runtime/src/lib.rs` | wasm | 35 | 🟡 WASM example |

#### Logging (7 tests)
| File | Test | Line | Status |
|------|------|------|--------|
| `log/src/lib.rs` | log example | 12 | 🟡 Logging setup |
| `log/src/lib.rs` | `cleanup_old_logs` | 175 | 🟡 Cleanup |
| `log/src/lib.rs` | `init` | 65 | 🟡 Init |
| `log/src/lib.rs` | `init_dual` | 124 | 🟡 Dual logging |
| `log/src/lib.rs` | `init_with_filter` | 84 | 🟡 Filtered logging |
| `log/src/parse/mod.rs` | parse | 12 | 🟡 Log parsing |
| `log/src/run_time/mod.rs` | run_time | 12 | 🟡 Runtime |

#### SIMD/SQP (4 tests)
| File | Test | Line | Status |
|------|------|------|--------|
| `simd/src/lib.rs` | simd | 22 | 🟡 SIMD example |
| `sqp/src/lib.rs` | sqp | 13 | 🟡 Query example |
| `sqp/src/raw.rs` | `raw` | 80 | 🟡 Raw query |
| `sqp/src/raw.rs` | `raw_with` | 94 | 🟡 Raw with params |

**Action Required:** Apply doc-test fix methodology from `doc/report/doctest_fixes_final_2026-01-21.md`

---

## Priority 4: Not Yet Implementable (Placeholder Tests)

### 4.1 Decorators Module

**Status:** 🔴 PARSING ERROR + INCOMPLETE IMPLEMENTATION
**Implementation:** `src/lib/std/src/core/decorators.spl` (has syntax errors)
**Tests:** `test/lib/std/unit/core/decorators_spec.spl` (10 skip tests)
**Effort:** ~4-6 hours (fix parsing + implement missing decorators)

#### All Tests Skipped (10 features)
| Feature | Test | Status |
|---------|------|--------|
| @cached - caches results | decorators_spec.spl:10 | 🔴 Module broken |
| @cached - different arguments | decorators_spec.spl:12 | 🔴 Module broken |
| @logged - logs calls | decorators_spec.spl:17 | 🔴 Not implemented |
| @logged - includes return | decorators_spec.spl:19 | 🔴 Not implemented |
| @deprecated - warning | decorators_spec.spl:23 | 🔴 Not implemented |
| @deprecated - replacement msg | decorators_spec.spl:25 | 🔴 Not implemented |
| @timeout - raises error | decorators_spec.spl:29 | 🔴 Not implemented |
| @timeout - returns on time | decorators_spec.spl:31 | 🔴 Not implemented |
| Composition - multiple | decorators_spec.spl:35 | 🔴 Not implemented |
| Composition - correct order | decorators_spec.spl:37 | 🔴 Not implemented |

**Blockers:**
1. Parsing error in `decorators.spl`: "Unexpected token: expected match arm, found LParen"
2. Only `@cached` is partially implemented
3. Missing: `@logged`, `@deprecated`, `@timeout`

**Action Required:**
1. Fix syntax error in decorators.spl
2. Implement missing decorators
3. Test decorator composition

---

### 4.2 Synchronization Module

**Status:** ✅ IMPLEMENTED but ⚠️ TESTS HAVE CHALLENGES
**Implementation:** `src/lib/std/src/core/synchronization.spl` (324 lines, 4 classes)
**Tests:** `test/lib/std/unit/core/synchronization_spec.spl` (4 skip tests)
**Effort:** ~2-3 hours (design testable API or add test hooks)

#### All Implementation Complete (4 features)
| Feature | Class | Test | Status |
|---------|-------|------|--------|
| Atomic operations | `Atomic` | sync_spec.spl | ⚠️ Test strategy needed |
| Mutex locking | `Mutex` | sync_spec.spl | ⚠️ Test strategy needed |
| RwLock read/write | `RwLock` | sync_spec.spl | ⚠️ Test strategy needed |
| Semaphore counting | `Semaphore` | sync_spec.spl | ⚠️ Test strategy needed |

**Challenge:** Previous attempt failed because tests need to verify internal state, but classes don't expose internal state for inspection.

**Options:**
1. Add test-only inspection methods (e.g., `debug_get_count()`)
2. Add `#[cfg(test)]` conditional compilation
3. Test only observable behavior (harder but more realistic)

**Action Required:**
1. Choose testing strategy
2. Update classes with inspection hooks if needed
3. Implement tests

---

## Summary Statistics

### Immediate Impact (Priority 1)
| Module | Tests | Effort | Impact |
|--------|-------|--------|--------|
| Math | 29 | 2 hours | High (core functionality) |
| Random | 12 | 1.5 hours | High (core functionality) |
| Regex | 1 | 15 min | Low (edge case) |
| **Total P1** | **42** | **~3.75 hours** | **Enable 42 tests** |

### Short-term (Priority 2-3)
| Category | Tests | Effort | Impact |
|----------|-------|--------|--------|
| Rust #[ignore] | 3 | 0 hours | None needed (working) |
| Doc-tests | 31 | 6-9 hours | Documentation quality |
| **Total P2-3** | **34** | **6-9 hours** | **Enable 31 doc examples** |

### Medium-term (Priority 4)
| Module | Tests | Effort | Impact |
|--------|-------|--------|--------|
| Decorators | 10 | 4-6 hours | Fix module + add features |
| Synchronization | 4 | 2-3 hours | Testing strategy |
| **Total P4** | **14** | **6-9 hours** | **Fix 14 features** |

### Overall Summary
| Priority | Tests | Effort | Status |
|----------|-------|--------|--------|
| **P1: Ready** | 42 | 3.75 hrs | ✅ Just enable |
| **P2-3: Doc-tests** | 34 | 6-9 hrs | 🟡 Fix examples |
| **P4: Blocked** | 14 | 6-9 hrs | 🔴 Need implementation |
| **TOTAL** | **90** | **15-21 hrs** | **90 features** |

**Excluded:** 935 placeholder tests for unimplemented features (macros, tree-sitter, game engine, etc.)

---

## Recommended Action Plan

### Phase 1: Quick Wins (Today - 3.75 hours)
1. **Math module** (2 hours)
   - Remove all skip tags from `test/lib/std/unit/core/math_spec.spl`
   - Run tests: `./target/debug/simple test math`
   - Fix any failures

2. **Random module** (1.5 hours)
   - Remove all skip tags from `test/lib/std/unit/core/random_spec.spl`
   - Run tests: `./target/debug/simple test random`
   - Fix any failures

3. **Regex edge case** (15 min)
   - Define overlapping match behavior
   - Write test case

**Impact:** +42 tests passing (4.5% reduction in skipped tests)

### Phase 2: Documentation (This Week - 6-9 hours)
1. **Compiler doc-tests** (1-2 hours)
   - Fix 4 doc-tests in compiler crate

2. **Runtime doc-tests** (2-3 hours)
   - Fix 10 doc-tests for FFI examples

3. **Infrastructure doc-tests** (3-4 hours)
   - Fix 17 doc-tests across various crates

**Impact:** +31 doc examples working

### Phase 3: Blocked Features (Next Week - 6-9 hours)
1. **Fix decorators module** (4-6 hours)
   - Fix parsing error
   - Implement `@logged`, `@deprecated`, `@timeout`
   - Enable 10 tests

2. **Synchronization testing** (2-3 hours)
   - Design testing strategy
   - Implement 4 tests

**Impact:** +14 tests passing

---

## Success Metrics

### Current State
- Total tests: 7,909
- Skipped: 1,004 (12.7%)
- Passing: ~6,905 (87.3%)

### After Phase 1 (Quick Wins)
- Skipped: 962 (12.2%)
- Passing: ~6,947 (87.8%)
- **Improvement:** 42 tests (+0.5%)

### After Phase 2 (Doc-tests)
- Skipped: 962 (12.2%) - unchanged
- Doc-tests ignored: 0 (down from 31)
- **Improvement:** Better documentation

### After Phase 3 (Blocked Features)
- Skipped: 948 (12.0%)
- Passing: ~6,961 (88.0%)
- **Improvement:** +56 total tests (+0.7%)

### Final Target
- **-56 skipped tests** (5.6% reduction in skip count)
- **+56 passing tests** (0.7% increase in pass rate)
- **-31 ignored doc-tests** (100% reduction in doc-test ignores)

---

## Implementation Notes

### Math Module
- All functions use either pure Simple implementations or FFI
- Tests use tolerance-based comparisons for floats
- Newton's method for `sqrt()`, Taylor series for `sin()`/`cos()`/`exp()`

### Random Module
- LCG (Linear Congruential Generator) implementation
- Global state management with lazy initialization
- Box-Muller transform for normal distribution

### Regex Module
- Only one edge case needs clarification
- Main implementation is complete (1400 lines, 25 exports)

### Doc-Tests
- Follow methodology from `doc/report/doctest_fixes_final_2026-01-21.md`
- Read actual code, verify API, create working examples
- Use `no_run` only when execution requires external resources

### Decorators
- Fix syntax error first
- Reference existing `@cached` implementation as template
- Implement using wrapper functions/classes

### Synchronization
- Consider adding test-specific inspection methods
- Alternative: Test only observable behavior
- Document testing strategy for future concurrent features

---

## Related Documentation

- `doc/report/implementable_skipped_tests_2026-01-21.md` - Original analysis
- `doc/report/doctest_fixes_final_2026-01-21.md` - Doc-test fix methodology
- `doc/report/ignored_tests_feature_2026-01-21.md` - Rust #[ignore] tests
- `doc/test/test_result.md` - Current test results
- `doc/feature/pending_feature.md` - All incomplete features

---

**Generated:** 2026-01-21
**Total Implementable Features:** 90 (42 immediate + 31 doc-tests + 14 blocked + 3 already working)
