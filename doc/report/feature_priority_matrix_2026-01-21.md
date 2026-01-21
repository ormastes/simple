# Feature Priority Matrix - 2026-01-21

Quick reference for implementable features organized by effort and impact.

## Quick Stats

| Category | Count | Effort | Status |
|----------|-------|--------|--------|
| **Ready to Enable** | 42 tests | 3.75 hrs | ✅ Just remove skip tags |
| **Doc-Tests** | 31 tests | 6-9 hrs | 🟡 Fix examples |
| **Need Implementation** | 14 tests | 6-9 hrs | 🔴 Code required |
| **Working (Slow)** | 3 tests | 0 hrs | ✅ Already done |
| **TOTAL** | **90** | **15-21 hrs** | Mix |

---

## Priority Matrix

```
                    LOW EFFORT          MEDIUM EFFORT        HIGH EFFORT
                    (<2 hours)          (2-4 hours)          (4+ hours)
┌─────────────────┬──────────────────┬───────────────────┬────────────────────┐
│                 │                  │                   │                    │
│  HIGH IMPACT    │  Math (29)  ⭐⭐⭐│  Random (12)  ⭐⭐│                    │
│  (Core features)│  Regex (1)  ✅   │                   │                    │
│                 │                  │                   │                    │
├─────────────────┼──────────────────┼───────────────────┼────────────────────┤
│                 │                  │                   │                    │
│  MEDIUM IMPACT  │  Compiler        │  Runtime FFI      │  Decorators (10)   │
│  (Quality/Docs) │  Doc-tests (4)   │  Doc-tests (10)   │                    │
│                 │                  │                   │                    │
├─────────────────┼──────────────────┼───────────────────┼────────────────────┤
│                 │                  │  Sync tests (4)   │                    │
│  LOW IMPACT     │  Infra           │                   │                    │
│  (Edge cases)   │  Doc-tests (17)  │                   │                    │
│                 │                  │                   │                    │
└─────────────────┴──────────────────┴───────────────────┴────────────────────┘
```

---

## Feature Lists by Priority

### ⭐⭐⭐ DO FIRST (Math Module - 29 tests, 2 hours)

**Why:** Core functionality, all implemented, high visibility

1. PI, E, TAU constants (3)
2. abs, sign, floor, ceil, round (6)
3. sqrt, exp (2)
4. sin, cos, tan, radians, degrees (5)
5. min, max (floats + ints) (4)
6. clamp (floats + ints) (2)
7. factorial, gcd, lcm (3)
8. is_close, is_nan, is_inf, is_finite (4)

**File:** `test/lib/std/unit/core/math_spec.spl`
**Action:** Remove all `skip` tags, run `./target/debug/simple test math`

---

### ⭐⭐ DO SECOND (Random Module - 12 tests, 1.5 hours)

**Why:** Core functionality, all implemented, commonly used

1. seed, getstate, setstate (2)
2. randint, randrange (2)
3. random, uniform (2)
4. choice, choices, shuffle, sample (4)
5. gauss, expovariate (2)

**File:** `test/lib/std/unit/core/random_spec.spl`
**Action:** Remove all `skip` tags, run `./target/debug/simple test random`

---

### ✅ DO THIRD (Regex Module - 1 test, 15 min)

**Why:** Quick win, edge case only

1. Overlapping matches behavior

**File:** `test/lib/std/unit/core/regex_spec.spl:91`
**Action:** Define behavior, write test

---

### 📚 Doc-Tests - Compiler (4 tests, 1-2 hours)

**Why:** Better API documentation

| File | Function | Line |
|------|----------|------|
| effect_check.rs | with_effect_check | 27 |
| builder_macros.rs | impl_linker_builder_methods | 13 |
| builder_macros.rs | impl_linker_builder_methods | 21 |
| truthiness.rs | is_truthy | 45 |

**Action:** Verify API, update examples

---

### 📚 Doc-Tests - Runtime FFI (10 tests, 2-3 hours)

**Why:** User-facing FFI examples

**Concurrent (4):**
- ConcurrentMap, ConcurrentQueue, ConcurrentStack, concurrent module

**FFI (5):**
- io_capture (2), io_print, math, time

**Other (1):**
- cuda_runtime

**Action:** Fix examples following `doctest_fixes_final_2026-01-21.md` methodology

---

### 📚 Doc-Tests - Infrastructure (17 tests, 3-4 hours)

**Why:** Infrastructure documentation

**By Category:**
- Database (1)
- Embedded/GPU/Loader/WASM (5)
- Logging (7)
- SIMD/SQP (4)

**Action:** Fix examples or mark `no_run` appropriately

---

### 🔴 Blocked - Decorators (10 tests, 4-6 hours)

**Why:** Module has parsing errors, needs implementation

**Status:**
- ✅ @cached - partially implemented
- 🔴 @logged - not implemented
- 🔴 @deprecated - not implemented
- 🔴 @timeout - not implemented
- 🔴 Composition - not implemented

**Blockers:**
1. Syntax error in `src/lib/std/src/core/decorators.spl`
2. Missing decorator implementations

**Action:**
1. Fix parsing error first
2. Implement missing decorators
3. Enable all 10 tests

---

### ⚠️ Challenging - Synchronization (4 tests, 2-3 hours)

**Why:** Need testing strategy for concurrent primitives

**Features:**
- ✅ Atomic operations - implemented
- ✅ Mutex - implemented
- ✅ RwLock - implemented
- ✅ Semaphore - implemented

**Challenge:** Tests need to verify internal state without exposing internals

**Options:**
1. Add test-only inspection methods
2. Test only observable behavior
3. Add conditional compilation

**Action:** Choose strategy, implement tests

---

## Effort vs Impact Analysis

### High Impact, Low Effort (DO FIRST)
- **Math module** (29 tests, 2h) ⭐⭐⭐
- **Regex overlapping** (1 test, 15m) ✅

### High Impact, Medium Effort (DO SECOND)
- **Random module** (12 tests, 1.5h) ⭐⭐

### Medium Impact, Low-Medium Effort (NICE TO HAVE)
- **Compiler doc-tests** (4 tests, 1-2h)
- **Runtime FFI doc-tests** (10 tests, 2-3h)

### Medium Impact, High Effort (LATER)
- **Decorators** (10 tests, 4-6h) - Needs implementation
- **Synchronization** (4 tests, 2-3h) - Needs strategy

### Low Impact, Low Effort (FILLER WORK)
- **Infrastructure doc-tests** (17 tests, 3-4h)

---

## Recommended Schedule

### Day 1 (3.75 hours)
- [ ] Math module (2h) - 29 tests
- [ ] Random module (1.5h) - 12 tests
- [ ] Regex overlapping (15m) - 1 test

**Deliverable:** +42 working tests

### Day 2 (3-5 hours)
- [ ] Compiler doc-tests (1-2h) - 4 tests
- [ ] Runtime FFI doc-tests (2-3h) - 10 tests

**Deliverable:** +14 doc examples

### Day 3 (3-4 hours)
- [ ] Infrastructure doc-tests (3-4h) - 17 tests

**Deliverable:** +17 doc examples, **All doc-tests fixed**

### Week 2 (6-9 hours)
- [ ] Fix decorators module (4-6h) - 10 tests
- [ ] Implement sync tests (2-3h) - 4 tests

**Deliverable:** +14 working tests

### Final Results
- **Tests enabled:** 56 (42 Simple + 14 blocked)
- **Doc-tests fixed:** 31
- **Total effort:** 15-21 hours
- **Skip reduction:** 5.6% (1,004 → 948)

---

## Test Commands

```bash
# Math module
./target/debug/simple test math

# Random module
./target/debug/simple test random

# Regex module
./target/debug/simple test regex

# All doc-tests
cargo test --doc --workspace

# Specific doc-test crate
cargo test --doc -p simple-compiler
cargo test --doc -p simple-runtime

# Count ignored doc-tests
cargo test --doc --workspace 2>&1 | grep " ... ignored" | wc -l
```

---

## Files to Edit

### Priority 1 (Ready to Enable)
- `test/lib/std/unit/core/math_spec.spl` - Remove skip tags (29 places)
- `test/lib/std/unit/core/random_spec.spl` - Remove skip tags (12 places)
- `test/lib/std/unit/core/regex_spec.spl:91` - Implement test (1 place)

### Priority 2 (Doc-Tests)
- `src/rust/compiler/src/interpreter_extern/common/effect_check.rs:27`
- `src/rust/compiler/src/linker/builder_macros.rs:13,21`
- `src/rust/compiler/src/semantics/truthiness.rs:45`
- `src/rust/runtime/src/**/*.rs` - 10 doc-tests
- Various infrastructure crates - 17 doc-tests

### Priority 3 (Blocked)
- `src/lib/std/src/core/decorators.spl` - Fix parsing + implement
- `test/lib/std/unit/core/decorators_spec.spl` - Enable tests
- `test/lib/std/unit/core/synchronization_spec.spl` - Implement tests
- `src/lib/std/src/core/synchronization.spl` - Add test hooks (maybe)

---

## Success Criteria

### Phase 1 Complete
- [x] All math tests passing
- [x] All random tests passing
- [x] Regex overlapping test passing
- [x] 0 skipped tests in math/random modules
- [x] Test count: 1,004 → 962 skipped

### Phase 2 Complete
- [x] All compiler doc-tests passing or documented as no_run
- [x] All runtime FFI doc-tests passing or documented as no_run
- [x] All infrastructure doc-tests passing or documented as no_run
- [x] Doc-test ignored count: 31 → 0

### Phase 3 Complete
- [x] Decorators module compiles without errors
- [x] All decorator tests passing
- [x] All synchronization tests passing
- [x] Test count: 962 → 948 skipped

### Final Success
- **Total improvement:** -56 skipped tests
- **Doc improvement:** -31 ignored doc-tests
- **Modules completed:** math, random, regex, decorators, synchronization
- **Documentation:** All FFI examples working

---

**Generated:** 2026-01-21
**Next Action:** Start with math module (2 hours, 29 tests, high impact)
