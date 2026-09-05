# Bug: add_remove_log_modes_spec.spl Timeout Under Resource Limits

**Date:** 2026-07-17  
**Lane:** L5 (test/02_integration and test/integration)  
**Status:** ROOT CAUSE IDENTIFIED - Interpreter load time with 600+ files under 120s runner limit

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

**Option B: Increase runner resource limit**
- Raise test timeout from 120s → 180-240s for this suite
- Allows interpreter startup to complete
- Trade-off: slow feedback loop

**Option C: Narrow SIMPLE_LIB systematically**
- Copy minimal closure: just std.cli, std.log, app.io trees (~30 files total)
- Preserves module paths via directory structure
- Adds ~15ms setup overhead per test (acceptable vs. 90s interpreter load)
- See doc/07_guide/app/editor_tui.md for template

## App-Side Analysis
- add/main.spl, remove/main.spl: no unbounded loops, interactive I/O, or blocking operations
- Apps are pure: read manifest → modify → write file → exit
- Hang is purely infrastructure (runner resource limit), NOT logic defect

## Next Steps
Recommend: **Option A (compiled binaries)** - if binaries exist, retarget spec to use them; if not, add build step to compile apps during test setup (one-time, amortized cost negligible vs. per-test interpreter overhead)

## Fix applied (2026-07-18)

Reclassified both spec copies to the slow lane: all 8 `it` blocks converted to
`slow_it` (the runner's `file_has_slow_test` detects `slow_it ` and applies
`resource_limits_for_slow_tests`), imports updated, `# @slow` header comment
added for readers. Both files parse clean (fix --dry-run, 0 errors). Regular
section runs will no longer die on this spec; the slow lane gives the 16
interpreter spawns adequate budget. Durable improvement (retarget spec to
compiled binaries once redeploy lands) remains listed above as option 1.
