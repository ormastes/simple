# Bug: skip_it causes interpreter exit code 1

**Status:** Identified  
**Severity:** Medium
**Discovered:** 2026-01-30

## Summary

The `skip_it` function in the test framework causes the interpreter subprocess to exit with code 1, even when all other tests pass. This makes test files with skipped tests appear to fail.

## Reproduction

```simple
describe "Test with skip":
    it "passes":
        expect 1 == 1
    
    skip_it "skipped test":
        expect false
```

**Result:** Process exits with code 1, marked as FAIL

## Affected Files

- `test/lib/std/system/bugs/interpreter_bugs_spec.spl` (4 passed, exit 1)
- `test/lib/std/system/improvements/parser_improvements_spec.spl` (16 passed, exit 1)  
- `test/lib/std/system/spec/matchers/spec_matchers_spec.spl` (11 passed, exit 1)

All tests in these files pass, but the presence of `skip_it` causes failure.

## Root Cause

The `skip_it` function (defined in `src/lib/std/src/spec/dsl.spl:154`) creates a skipped Example, but something in the cleanup or finalization causes the interpreter to exit with code 1.

## Workaround

1. Replace `skip_it` with regular `it` and add explicit skip logic
2. Or comment out `skip_it` tests temporarily
3. Or remove `skip_it` tests from affected files

## Fix Needed

Investigate why skipped tests cause non-zero exit codes. Possible causes:
- Skip tracking state not cleaned up properly
- Assertion in test framework expecting no skipped tests
- GC issue with skipped test closures
