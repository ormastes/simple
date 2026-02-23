# Ignored Tests Database Status - 2026-01-21

## Current State

**Database entries:** 1
**Ignored tests in DB:** **0**
**Ignored percentage:** **0.0%**

## Why the 4 ignored tests are NOT in the database

The 4 `ignore_it` tests with "slow" in their names exist in source code but are **not tracked in the database** because:

### Root Cause: Compilation Failures

1. **test/integration/spec/runner_spec.spl** (contains 2 ignored tests)
   - Status: `failed`
   - Error: `semantic: variable 'hook_order' not found`
   - Database entry: Recorded as 1 failed file, individual tests not parsed

2. **test/unit/spec/dsl_spec.spl** (contains 2 ignored tests)
   - Status: Not in database (not even attempted to run)
   - Error: Parse errors in the file
   - Database entry: None

### How Test Database Works

```
┌─────────────────┐
│ Test File       │
├─────────────────┤
│ ✅ Compiles     │ → Execute → Parse output → Record individual tests
│ ❌ Fails        │ → Record 1 failed entry → Individual tests NOT recorded
└─────────────────┘
```

## Current Database Content

```sdn
tests |test_id, test_name, test_file, category, status, ...|
    test/integration/spec/runner_spec.spl, runner_spec, ..., Integration, failed, ...
```

**Only 1 entry** - the failed compilation of runner_spec, not the 4 individual ignored tests inside it.

## The 4 Ignored Tests (in source, not in DB)

| File | Line | Test Name | Status |
|------|------|-----------|--------|
| test/unit/spec/dsl_spec.spl | 115 | "registers a slow example" | NOT in DB |
| test/unit/spec/dsl_spec.spl | 124 | "skips slow test when RUN_SLOW_TESTS is not set" | NOT in DB |
| test/integration/spec/runner_spec.spl | 189 | "skips slow tests by default" | NOT in DB |
| test/integration/spec/runner_spec.spl | 202 | "runs slow tests when enabled" | NOT in DB |

## What Needs to Happen

To get these 4 ignored tests into the database with `status = ignored`:

1. **Fix compilation errors** in runner_spec.spl (variable `hook_order` not found)
2. **Fix compilation errors** in dsl_spec.spl (parse errors)
3. **Run tests successfully** - the test runner will then:
   - Parse test output: "22 examples, 0 failures, 0 pending, 4 ignored"
   - Create TestFileResult with `ignored = 4`
   - Store in database with `TestStatus::Ignored`

## Infrastructure Status

✅ **All tracking infrastructure is complete:**
- Test structures have `ignored` field
- Parser extracts ignored count from output
- Database records `TestStatus::Ignored`
- Reports show ignored percentage

❌ **Missing: Tests that actually compile and run**

## Expected Output (once fixed)

```sdn
tests |test_id, test_name, test_file, category, status, ...|
    test/integration/spec/runner_spec.spl, runner_spec, ..., Integration, ignored, ...
    test/unit/spec/dsl_spec.spl, dsl_spec, ..., Unit, ignored, ...
```

```markdown
| 🔕 Ignored | 4 | 18.2% |  # 4 out of 22 total tests
```

## Conclusion

**Status: Infrastructure ✅ Complete | Database ❌ Empty (0 ignored tests)**

The 4 ignored tests exist in source code but cannot be tracked in the database until the containing test files compile successfully.
