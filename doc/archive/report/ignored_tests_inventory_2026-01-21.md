# Ignored Tests Inventory

**Date:** 2026-01-21
**Database:** doc/test/test_db.sdn
**Database Status:** Currently contains only 1 record (runner_spec - failed)

---

## Summary

**Total Ignored Test Definitions in Code:** 11
- **slow_it:** 7 tests (would be ignored at Rust level by default)
- **ignore_it:** 4 tests (intentionally disabled, never run)

**Tests with "long" in description:** 1
- `slow_it "takes a long time"` in `test/unit/spec/dsl_spec.spl`

---

## Detailed Inventory

### slow_it Tests (7 total)

| # | Test Description | File | Has "long"? |
|---|------------------|------|-------------|
| 1 | **"takes a long time"** | test/unit/spec/dsl_spec.spl | ✅ **YES** |
| 2 | "takes forever" | test/unit/spec/dsl_spec.spl | ❌ No |
| 3 | "slow test" | test/integration/spec/runner_spec.spl | ❌ No |
| 4 | "slow test" | test/integration/spec/runner_spec.spl | ❌ No |
| 5 | "generates all 15 Lean files" | test/lib/std/unit/verification/regeneration_spec.spl | ❌ No |
| 6 | "includes all project paths" | test/lib/std/unit/verification/regeneration_spec.spl | ❌ No |
| 7 | "all generated files have valid Lean header" | test/lib/std/unit/verification/regeneration_spec.spl | ❌ No |

### ignore_it Tests (4 total)

| # | Test Description | File | Has "long"? |
|---|------------------|------|-------------|
| 1 | "registers a slow example" | test/unit/spec/dsl_spec.spl | ❌ No |
| 2 | "skips slow test when RUN_SLOW_TESTS is not set" | test/unit/spec/dsl_spec.spl | ❌ No |
| 3 | "skips slow tests by default" | test/integration/spec/runner_spec.spl | ❌ No |
| 4 | "runs slow tests when enabled" | test/integration/spec/runner_spec.spl | ❌ No |

---

## Code Locations

### test/unit/spec/dsl_spec.spl (4 total: 2 slow_it, 2 ignore_it)

```simple
context "slow_it":
    ignore_it "registers a slow example":
        describe "Test":
            slow_it "takes a long time":  ← HAS "long"
                pass

    ignore_it "skips slow test when RUN_SLOW_TESTS is not set":
        describe "Test":
            slow_it "takes forever":
                pass
```

### test/integration/spec/runner_spec.spl (4 total: 2 slow_it, 2 ignore_it)

```simple
ignore_it "skips slow tests by default":
    describe "Sample":
        it "fast test":
            pass
        slow_it "slow test":
            pass

ignore_it "runs slow tests when enabled":
    describe "Sample":
        it "fast test":
            pass
        slow_it "slow test":
            pass
```

### test/lib/std/unit/verification/regeneration_spec.spl (3 total: all slow_it)

```simple
describe "Verification Regeneration Module":
    context "regenerate() function":
        slow_it "generates all 15 Lean files":
            pass

        slow_it "includes all project paths":
            pass

        slow_it "all generated files have valid Lean header":
            pass
```

---

## Why Database is Empty

The test database currently only has 1 record because:

1. **Tests haven't been run yet** - Most tests need to be executed to appear in database
2. **Parse errors** - Some test files have syntax errors preventing execution:
   - `runner_spec.spl` - Failed with "function `env` not found"
   - `dsl_spec.spl` - May have parse issues

3. **Default behavior** - `slow_it` tests are skipped by default (not run unless `--only-slow`)

---

## To Populate Database with Ignored Tests

### Option 1: Run All Tests (will skip slow_it by default)
```bash
./target/debug/simple test test/
```

**Result:**
- `ignore_it` tests → recorded as `status="ignored"` (never run)
- `slow_it` tests → recorded as `status="ignored"` (skipped by default)

### Option 2: Run Only Slow Tests
```bash
./target/debug/simple test test/ --only-slow
```

**Result:**
- `slow_it` tests → recorded as `status="passed"` or `status="failed"` (actually run)
- `ignore_it` tests → still recorded as `status="ignored"` (never run)

### Option 3: List All Ignored Tests Without Running
```bash
./target/debug/simple test test/ --list-ignored
```

**Result:** Shows all tests marked with `slow_it` or `ignore_it`, but doesn't update database

---

## Expected Database After Full Test Run

If all tests were executed successfully, the database would contain:

```sdn
tests |test_id, test_name, ..., status, ...|
    test/unit/spec/dsl_spec.spl, dsl_spec, ..., ignored, ...
    test/integration/spec/runner_spec.spl, runner_spec, ..., ignored, ...
    test/lib/std/unit/verification/regeneration_spec.spl, regeneration_spec, ..., ignored, ...
```

**Note:** File-level status would be "ignored" if ANY test in that file is ignored.

---

## Grep Commands for Finding Tests

```bash
# Count all slow_it tests
grep -r "slow_it \"" test/ --include="*.spl" | wc -l
# Output: 7

# Count all ignore_it tests
grep -r "ignore_it \"" test/ --include="*.spl" | wc -l
# Output: 4

# Find tests with "long" in description
grep -r "slow_it \".*long" test/ --include="*.spl"
# Output: test/unit/spec/dsl_spec.spl:                slow_it "takes a long time":

# Find tests with "long" in ignore_it
grep -r "ignore_it \".*long" test/ --include="*.spl"
# Output: (none)
```

---

## Answer to Original Question

**Q: How many ignored tests?**
**A: 11 total** (7 slow_it + 4 ignore_it)

**Q: How many of the 4 ignore_it tests have "long" word?**
**A: 0** (none of the ignore_it tests have "long")

**Q: How many ignored tests have "long" word?**
**A: 1** - Only `slow_it "takes a long time"` in dsl_spec.spl

---

## Note on Nested Tests

Some `ignore_it` tests contain `slow_it` tests nested inside them:

```simple
ignore_it "registers a slow example":
    describe "Test":
        slow_it "takes a long time":  # This is INSIDE an ignore_it
            pass
```

When counted:
- **As definitions:** 1 ignore_it + 1 slow_it = 2 tests
- **When run:** Neither executes (outer ignore_it prevents execution)
- **In database:** Would be recorded as 1 file with status="ignored"

The inventory above counts **definitions**, not execution behavior.
