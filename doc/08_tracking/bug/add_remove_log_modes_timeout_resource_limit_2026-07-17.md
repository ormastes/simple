# Bug: add_remove_log_modes_spec.spl Timeout Under Resource Limits
## Closed 2026-11-25 — slow-lane fix verified; Windows cmd caret-escape harness defect fixed

**Date:** 2026-07-17  
**Lane:** L5 (test/02_integration and test/integration)  
**Status:** RESOLVED (2026-11-25) — see verification note at end of file

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


## Verification 2026-11-25 (Windows, worktree wt-p3-baa)

Ran the surviving spec copy with the tracked self-hosted binary:

```
SIMPLE_LIB=src bin/simple.exe test test/02_integration/app/add_remove_log_modes_spec.spl --mode=interpreter
```

- **Timeout: RESOLVED.** The slow-lane conversion (`slow_it`, 2026-07-18) holds:
  the full 8-example file completes in ~80 s wall clock with no resource-limit
  timeout (previously 120 s timeout at 0/8). The twin
  `test/integration/app/add_remove_log_modes_spec.spl` no longer exists in the
  tree; `test/02_integration/app/` is the only copy.
- **New defect found and fixed during verification:** the first run failed
  1/8 — `supports add log-mode json` expected `"constraint":"^1.0.0"` but the
  app received `1.0.0`. Root cause: the spec's Windows `_spawn_cli` branch
  builds a `cmd.exe /c` command line, and cmd treats `^` as an escape
  character, eating the caret in `beta@^1.0.0` before the child saw it. Fixed
  in the spec harness by doubling `^` in the cmd branch
  (`joined.replace("^", "^^")`); no assertion was changed. After the fix:
  `executed=8 passed=8 failed=0`, exit 0, ~79 s.
