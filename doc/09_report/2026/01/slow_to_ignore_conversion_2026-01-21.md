# Conversion of slow_it to ignore_it Tests

**Date:** 2026-01-21
**Task:** Convert test definitions from `slow_it` to `ignore_it` in dsl_spec.spl and runner_spec.spl

---

## Summary of Changes

### Before
- **Total ignored tests:** 11 (7 slow_it + 4 ignore_it)
- **Tests with "long":** 1 (slow_it "takes a long time")

### After
- **Total ignored tests:** 11 (3 slow_it + 8 ignore_it)
- **Tests with "long":** 1 (ignore_it "takes a long time")

### Files Modified
1. `test/unit/spec/dsl_spec.spl` - Converted 2 slow_it → ignore_it
2. `test/integration/spec/runner_spec.spl` - Converted 2 slow_it → ignore_it

---

## Detailed Changes

### test/unit/spec/dsl_spec.spl

#### Change 1: Context Name
```diff
- context "slow_it":
+ context "ignore_it":
```

#### Change 2: Test "takes a long time"
```diff
- ignore_it "registers a slow example":
+ ignore_it "registers an ignored example":
      describe "Test":
-         slow_it "takes a long time":
+         ignore_it "takes a long time":
              pass

      val groups = get_all_groups()
      val example = groups[0].test_examples[0]
-     expect(example.has_tag("slow")).to eq(true)
+     expect(example.is_ignored).to eq(true)
```

**Rationale:** Changed assertion from checking `slow` tag to checking `is_ignored` flag.

#### Change 3: Test "takes forever"
```diff
- ignore_it "skips slow test when RUN_SLOW_TESTS is not set":
-     # Note: This test assumes RUN_SLOW_TESTS is not set
-     # In real environment, we'd mock env.get()
+ ignore_it "ignored tests are never run":
+     # Ignored tests are intentionally disabled
      describe "Test":
-         slow_it "takes forever":
+         ignore_it "takes forever":
              pass

      val groups = get_all_groups()
      val example = groups[0].test_examples[0]
-     # Should be skipped unless RUN_SLOW_TESTS=1
-     val run_slow = env.get("RUN_SLOW_TESTS")
-     if run_slow != "1" and run_slow != "true":
-         expect(example.is_skipped).to eq(true)
+     # Should always be ignored
+     expect(example.is_ignored).to eq(true)
```

**Rationale:** Removed environment variable checking logic since ignore_it tests never run regardless of environment.

#### Change 4: Import Statement
```diff
- import spec.dsl.{describe, context, it, skip, slow_it, ignore_it, ...}
+ import spec.dsl.{describe, context, it, skip, ignore_it, ...}
```

**Rationale:** Removed `slow_it` from imports since it's no longer used in this file.

---

### test/integration/spec/runner_spec.spl

#### Change 1: Test "skips ignored tests"
```diff
- ignore_it "skips slow tests by default":
+ ignore_it "skips ignored tests":
      describe "Sample":
          it "fast test":
              pass
-         slow_it "slow test":
+         ignore_it "ignored test":
              pass

      val executor = TestExecutor.new()
      val results = executor.run()

-     # slow_it tests are skipped unless RUN_SLOW_TESTS=1
-     expect(results.skipped_count()).to gt(0)
+     # ignore_it tests are always skipped
+     expect(results.ignored_count()).to gt(0)
```

**Rationale:** Changed expectation from `skipped_count()` to `ignored_count()` to match the new test type.

#### Change 2: Test "ignored tests never run"
```diff
- ignore_it "runs slow tests when enabled":
+ ignore_it "ignored tests never run":
      describe "Sample":
          it "fast test":
              pass
-         slow_it "slow test":
+         ignore_it "ignored test":
              pass

-     val executor = TestExecutor.new().with_slow_tests(true)
+     val executor = TestExecutor.new()
```

**Rationale:** Removed `.with_slow_tests(true)` since ignore_it tests never run regardless of configuration.

---

## Remaining slow_it Tests

**Only 3 tests remain as slow_it** (all in `test/lib/std/unit/verification/regeneration_spec.spl`):

1. `slow_it "generates all 15 Lean files"`
2. `slow_it "includes all project paths"`
3. `slow_it "all generated files have valid Lean header"`

**Rationale for keeping these as slow_it:**
- These tests genuinely take a long time (10+ seconds)
- They test the verification.regenerate module which loads 15+ sub-modules
- Users may want to run them with `--only-slow` flag
- They should generate Rust `#[ignore]` attribute for selective execution

---

## Updated Inventory

### ignore_it Tests (8 total)

| # | Test Description | File | Has "long"? |
|---|------------------|------|-------------|
| 1 | "registers an ignored example" | test/unit/spec/dsl_spec.spl | ❌ No |
| 2 | **"takes a long time"** | test/unit/spec/dsl_spec.spl | ✅ **YES** |
| 3 | "ignored tests are never run" | test/unit/spec/dsl_spec.spl | ❌ No |
| 4 | "takes forever" | test/unit/spec/dsl_spec.spl | ❌ No |
| 5 | "skips ignored tests" | test/integration/spec/runner_spec.spl | ❌ No |
| 6 | "ignored test" | test/integration/spec/runner_spec.spl | ❌ No |
| 7 | "ignored tests never run" | test/integration/spec/runner_spec.spl | ❌ No |
| 8 | "ignored test" | test/integration/spec/runner_spec.spl | ❌ No |

### slow_it Tests (3 total)

| # | Test Description | File | Has "long"? |
|---|------------------|------|-------------|
| 1 | "generates all 15 Lean files" | test/lib/std/unit/verification/regeneration_spec.spl | ❌ No |
| 2 | "includes all project paths" | test/lib/std/unit/verification/regeneration_spec.spl | ❌ No |
| 3 | "all generated files have valid Lean header" | test/lib/std/unit/verification/regeneration_spec.spl | ❌ No |

---

## Answer to Updated Question

**Q: How many ignored tests total?**
**A: 11** (3 slow_it + 8 ignore_it)

**Q: How many of the ignore_it tests have "long" word?**
**A: 1** - `ignore_it "takes a long time"` in dsl_spec.spl

**Q: How many total tests have "long" word?**
**A: 1** (same test, now an ignore_it instead of slow_it)

---

## Testing Recommendations

### To verify ignore_it behavior:
```bash
# List all ignored tests
./target/debug/simple test test/ --list-ignored

# Should show 11 tests:
# - 8 ignore_it tests (never run)
# - 3 slow_it tests (skipped by default)
```

### To verify slow_it behavior:
```bash
# Run only slow tests
./target/debug/simple test test/lib/std/unit/verification/regeneration_spec.spl --only-slow

# Should run the 3 slow_it tests
```

---

## Semantic Differences

| Aspect | slow_it | ignore_it |
|--------|---------|-----------|
| **Purpose** | Long-running tests (>5s) | Intentionally disabled tests |
| **Default Behavior** | Skipped (generates #[ignore]) | Never run |
| **Can be run?** | Yes (with --only-slow) | No (always skipped) |
| **Tag** | Adds "slow" tag | Sets is_ignored flag |
| **Use Case** | Performance tests, integration tests | Broken tests, WIP features |
| **Database Status** | "ignored" (when skipped) | "ignored" (always) |

---

## Files Changed

1. **test/unit/spec/dsl_spec.spl**
   - Changed context name from "slow_it" to "ignore_it"
   - Converted 2 slow_it tests to ignore_it
   - Updated test assertions to check is_ignored
   - Removed slow_it from imports

2. **test/integration/spec/runner_spec.spl**
   - Converted 2 slow_it tests to ignore_it
   - Updated test expectations (skipped_count → ignored_count)
   - Removed .with_slow_tests(true) configuration

---

## Impact on Test Runner

### Before Changes
```
./target/debug/simple test --list-ignored
Ignored Tests:
  4 ignore_it tests
  7 slow_it tests (if not running with --only-slow)
```

### After Changes
```
./target/debug/simple test --list-ignored
Ignored Tests:
  8 ignore_it tests
  3 slow_it tests (if not running with --only-slow)
```

The total count remains 11, but the distribution changed to better reflect the semantic difference between "long-running" and "intentionally disabled" tests.
