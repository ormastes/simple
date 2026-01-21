# Quick Wins Checklist - 2026-01-21

Fast reference for immediately implementable features.

## TL;DR

**90 features can be implemented in 15-21 hours:**
- 42 tests ready (just remove `skip` tags) - 3.75 hours ⭐
- 31 doc-tests need fixes - 6-9 hours
- 14 tests need code - 6-9 hours
- 3 tests already work (slow tests, keep ignored)

---

## TODAY's Quick Wins (3.75 hours → 42 tests)

### Math Module (2 hours → 29 tests) ⭐⭐⭐

**File:** `test/lib/std/unit/core/math_spec.spl`
**Action:** Remove all `skip` tags

**Features:**
```
✅ PI, E, TAU                    # 3 tests
✅ abs, sign, floor, ceil, round # 6 tests
✅ sqrt, exp                     # 2 tests
✅ sin, cos, tan, degrees        # 5 tests
✅ min, max (int + float)        # 4 tests
✅ clamp (int + float)           # 2 tests
✅ factorial, gcd, lcm           # 3 tests
✅ is_close, is_nan, is_inf      # 4 tests
```

**Verification:**
```bash
# Remove skip tags
sed -i 's/skip "should/it "should/g' test/lib/std/unit/core/math_spec.spl

# Run tests
./target/debug/simple test math

# Expected: 29 tests pass
```

---

### Random Module (1.5 hours → 12 tests) ⭐⭐

**File:** `test/lib/std/unit/core/random_spec.spl`
**Action:** Remove all `skip` tags

**Features:**
```
✅ seed, getstate, setstate      # 2 tests
✅ randint, randrange             # 2 tests
✅ random, uniform                # 2 tests
✅ choice, choices, shuffle       # 4 tests
✅ gauss, expovariate             # 2 tests
```

**Verification:**
```bash
# Remove skip tags
sed -i 's/skip "should/it "should/g' test/lib/std/unit/core/random_spec.spl

# Run tests
./target/debug/simple test random

# Expected: 12 tests pass
```

---

### Regex Module (15 min → 1 test) ✅

**File:** `test/lib/std/unit/core/regex_spec.spl:91`
**Action:** Define behavior + write test

**Feature:**
```
⚠️ Handle overlapping matches
```

**Steps:**
1. Define: Does `"aa"` in `"aaaa"` return `["aa", "aa"]` or `["aa"]`?
2. Check regex engine implementation
3. Write test based on behavior
4. Remove `skip` tag

---

## Doc-Tests (6-9 hours → 31 tests)

### Compiler (1-2 hours → 4 tests)

```bash
src/rust/compiler/src/
├── interpreter_extern/common/effect_check.rs:27
├── linker/builder_macros.rs:13
├── linker/builder_macros.rs:21
└── semantics/truthiness.rs:45
```

**Action:** Read code → verify API → update examples

---

### Runtime FFI (2-3 hours → 10 tests)

```bash
src/rust/runtime/src/
├── concurrent/
│   ├── map.rs:55
│   ├── mod.rs:31
│   ├── queue.rs:28
│   └── stack.rs:31
├── value/ffi/
│   ├── io_capture.rs:16,30
│   ├── io_print.rs:16
│   ├── math.rs:17
│   └── time.rs:22
└── cuda_runtime.rs:30
```

**Action:** Fix examples or mark `no_run`

---

### Infrastructure (3-4 hours → 17 tests)

```bash
src/rust/
├── db/src/lib.rs:21
├── embedded/src/lib.rs:22
├── gpu/src/lib.rs:23
├── loader/src/lib.rs:16,22
├── wasm-runtime/src/lib.rs:35
├── log/src/
│   ├── lib.rs:12,65,84,124,175
│   ├── parse/mod.rs:12
│   └── run_time/mod.rs:12
├── simd/src/lib.rs:22
└── sqp/src/
    ├── lib.rs:13
    └── raw.rs:80,94
```

**Action:** Fix examples or mark `no_run`

---

## Blocked Features (6-9 hours → 14 tests)

### Decorators (4-6 hours → 10 tests) 🔴

**File:** `src/lib/std/src/core/decorators.spl`
**Blocker:** Parsing error + missing implementations

**Steps:**
1. Fix: "Unexpected token: expected match arm, found LParen"
2. Implement: `@logged`, `@deprecated`, `@timeout`
3. Test: decorator composition
4. Enable: 10 tests in `decorators_spec.spl`

**Features:**
```
✅ @cached (partial)
🔴 @logged (missing)
🔴 @deprecated (missing)
🔴 @timeout (missing)
🔴 Composition (missing)
```

---

### Synchronization (2-3 hours → 4 tests) ⚠️

**File:** `test/lib/std/unit/core/synchronization_spec.spl`
**Challenge:** Testing concurrent primitives

**Steps:**
1. Choose testing strategy:
   - Option A: Add test-only inspection methods
   - Option B: Test only observable behavior
   - Option C: Add conditional compilation
2. Implement 4 tests
3. Remove `skip` tags

**Features:**
```
✅ Atomic (impl exists, test needed)
✅ Mutex (impl exists, test needed)
✅ RwLock (impl exists, test needed)
✅ Semaphore (impl exists, test needed)
```

---

## Effort Breakdown

| Task | Tests | Hours | ROI |
|------|-------|-------|-----|
| **Math module** | 29 | 2.0 | ⭐⭐⭐ 14.5/hr |
| **Random module** | 12 | 1.5 | ⭐⭐⭐ 8.0/hr |
| **Regex overlapping** | 1 | 0.25 | ⭐⭐ 4.0/hr |
| **Compiler docs** | 4 | 1-2 | 🟡 2-4/hr |
| **Runtime docs** | 10 | 2-3 | 🟡 3-5/hr |
| **Infra docs** | 17 | 3-4 | 🟡 4-6/hr |
| **Decorators** | 10 | 4-6 | 🔴 1.7-2.5/hr |
| **Synchronization** | 4 | 2-3 | 🔴 1.3-2/hr |

**Best ROI:** Math module (14.5 tests per hour)

---

## Detailed Steps: Math Module

### Step 1: Locate skipped tests (1 min)
```bash
grep -n "skip" test/lib/std/unit/core/math_spec.spl
```

### Step 2: Remove skip tags (1 min)
```bash
# Manual: Replace all instances of:
#   context "X":
#       skip "should Y":
# with:
#   context "X":
#       it "should Y":

# OR use sed:
cd test/lib/std/unit/core
cp math_spec.spl math_spec.spl.bak
sed -i 's/skip "/it "/g' math_spec.spl
```

### Step 3: Run tests (1 min)
```bash
./target/debug/simple test math
```

### Step 4: Fix any failures (2 hours buffer)
If tests fail:
1. Check error message
2. Verify implementation in `src/lib/std/src/core/math.spl`
3. Fix test expectations or implementation
4. Re-run tests

### Step 5: Verify all passing (1 min)
```bash
# Should see:
# ✓ 29 tests passed
# ✗ 0 tests failed
```

---

## Detailed Steps: Random Module

Same as math module, but:
- File: `test/lib/std/unit/core/random_spec.spl`
- Implementation: `src/lib/std/src/core/random.spl`
- Expected: 12 tests pass

---

## Detailed Steps: Regex Overlapping

### Step 1: Check implementation (5 min)
```bash
# Read regex.spl findall implementation
grep -A 20 "fn findall" src/lib/std/src/core/regex.spl
```

### Step 2: Define behavior (2 min)
```
Question: What should happen with overlapping matches?

Example: Pattern "aa" in text "aaaa"

Option A: Return all matches ["aa", "aa"] (positions 0-2, 2-4)
Option B: Return non-overlapping ["aa", "aa"] (positions 0-2, 2-4)
Option C: Return first only ["aa"] (position 0-2)

Standard regex: Usually option C (first match, then continue after match)
```

### Step 3: Write test (5 min)
```simple
it "should handle overlapping matches":
    val regex = Regex.compile("(?=aa)")  # Lookahead for overlapping
    val matches = regex.findall("aaaa")
    # Based on chosen behavior:
    expect(matches.len()).to eq(3)  # if we support overlapping
    # OR
    expect(matches.len()).to eq(2)  # if we don't
```

### Step 4: Remove skip tag (1 min)

---

## Validation Commands

```bash
# Count skipped tests before
./target/debug/simple test --only-skipped --list | wc -l
# Expected: 1,004

# Run math tests
./target/debug/simple test math
# Expected: 29 passed

# Run random tests
./target/debug/simple test random
# Expected: 12 passed

# Count skipped tests after
./target/debug/simple test --only-skipped --list | wc -l
# Expected: 962 (1,004 - 29 - 12 - 1)

# Doc-tests before
cargo test --doc --workspace 2>&1 | grep " ... ignored" | wc -l
# Expected: 31

# Doc-tests after (when done)
cargo test --doc --workspace 2>&1 | grep " ... ignored" | wc -l
# Expected: 0
```

---

## Progress Tracking

### Phase 1: Quick Wins (Today)
- [ ] Math module (29 tests)
- [ ] Random module (12 tests)
- [ ] Regex overlapping (1 test)
- [ ] Total: 42 tests enabled

### Phase 2: Doc-Tests (This Week)
- [ ] Compiler (4 doc-tests)
- [ ] Runtime FFI (10 doc-tests)
- [ ] Infrastructure (17 doc-tests)
- [ ] Total: 31 doc-tests fixed

### Phase 3: Blocked (Next Week)
- [ ] Decorators (10 tests)
- [ ] Synchronization (4 tests)
- [ ] Total: 14 tests enabled

### Final Tally
- [ ] 56 Simple tests enabled
- [ ] 31 doc-tests fixed
- [ ] Skip count: 1,004 → 948 (-5.6%)
- [ ] Doc ignores: 31 → 0 (-100%)

---

## Common Issues & Solutions

### Issue: Tests fail with "function not found"
**Solution:** Check exports in implementation file
```bash
grep "^export" src/lib/std/src/core/math.spl
```

### Issue: Tests fail with type errors
**Solution:** Check test expectations match return types
```simple
# If function returns i32, test should use:
expect(result).to eq(42)  # not 42.0
```

### Issue: Float comparison failures
**Solution:** Use tolerance-based comparisons
```simple
# Bad:
expect(result).to eq(3.14159)

# Good:
expect(result > 3.14).to be_true()
expect(result < 3.15).to be_true()
```

### Issue: Doc-test compilation fails
**Solution:** Check API against source
```bash
# Read actual implementation
rg "pub fn function_name" src/rust/crate/src/

# Update doc-test to match
```

---

## Next Steps After Quick Wins

1. **Commit changes**
   ```bash
   jj bookmark set main -r @
   jj git push --bookmark main
   ```

2. **Update test database**
   ```bash
   ./target/debug/simple test  # Regenerates doc/test/test_db.sdn
   ```

3. **Check updated stats**
   ```bash
   cat doc/test/test_result.md
   cat doc/feature/pending_feature.md
   ```

4. **Start doc-tests**
   - Follow `doc/report/doctest_fixes_final_2026-01-21.md` methodology
   - Fix one crate at a time
   - Test after each fix

---

**Generated:** 2026-01-21
**Recommended:** Start with math module (highest ROI: 14.5 tests/hour)
