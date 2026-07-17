# Bug: add_remove_log_modes_spec.spl Timeout Under Resource Limits

**Date:** 2026-07-17  
**Lane:** L5 (test/02_integration and test/integration)  
**Status:** Blocking both test sections

## Symptom
Test runner times out after 120 seconds when attempting to run `test/02_integration/app/add_remove_log_modes_spec.spl` and `test/integration/app/add_remove_log_modes_spec.spl`.

Error message:
```
Error: Timed out under resource limits
```

Test setup completes quickly (~15ms), but the test itself hangs and consumes resources until timeout triggers.

## Minimal Repro
```bash
bin/simple test test/02_integration
# Times out on first test file after ~120 seconds
```

## Evidence
- test/02_integration: FAIL add_remove_log_modes_spec.spl (0 passed, 1 failed, 120013ms)
- test/integration: FAIL add_remove_log_modes_spec.spl (0 passed, 1 failed, 120014ms)
- Both sections blocked: 0 tests complete before timeout
- Identical timeout signature in both directories suggests shared root cause

## Suspected Layer
Test runner resource limit enforcement (self-protection), test executor, or test file itself.

## Impact
Blocks all lane L5 testing for both test/02_integration (~1088 tests) and test/integration (~612 tests).

## Notes
- Test daemon unavailable (fallback mode active)
- Resource governor configured: max memory per test 16GB, self-protection enabled
- Exact same spec file appears in both test sections and causes identical timeout
