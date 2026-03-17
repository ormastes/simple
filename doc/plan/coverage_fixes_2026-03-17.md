# Coverage Fixes — Plan

## Objective
Fix all remaining coverage tool issues so the entire pipeline works end-to-end with real data, correct file paths, and passing tests.

## Current Status
| Component | Status | Evidence |
|-----------|--------|----------|
| `bin/simple test --coverage` | Real | Prints summary, saves SDN |
| Decision probes (if/elif/while) | Real | 19 decisions tracked |
| Threshold enforcement | Real | `--threshold N` works |
| SDN file generation | Real | `build/coverage/coverage.sdn` written |
| File path tracking | Partial | 3/19 have real paths, 16 show `<source>` |
| Condition coverage (and/or) | Broken | 0 conditions in SDN |
| coverage_spec.spl | Broken | nil.not_empty crash |
| mcdc_spec.spl | Real | All tests pass |
| CoverageCollector methods | Real | All 16 methods implemented |

## What To Do

### Fix 1: coverage_spec.spl nil crash (difficulty: 1)
**File:** `src/lib/nogc_sync_mut/coverage.spl:50`
**Bug:** `rt_env_get("SIMPLE_COVERAGE_DATA")` returns nil, then `env_path.not_empty` crashes.
**Fix:** Guard with nil check: `if env_path != nil and env_path != "":`.

### Fix 2: File path `<source>` in SDN (difficulty: 3)
**Root cause:** `get_current_file()` thread-local returns None during evaluation.
`set_current_file()` is called in `exec_core.rs:745` but module loading at line 748 triggers sub-module evaluation which may clear/override the thread-local. The re-set at line 751 helps but decisions during import processing still get `<source>`.
**Fix:** Store file path in interpreter eval state (not thread-local). Add file tracking to the interpreter's `exec_node` dispatch so each node inherits the file from its parent module.
**Alternative (simpler):** In `record_decision_coverage_ffi`, if `current_file_for_coverage()` returns `<source>`, fall back to the Span's source info if available. Or track file in interpreter_control.rs `exec_if/while/match` using the span's module path.

### Fix 3: Condition coverage zero (difficulty: 2)
**Root cause:** `record_condition_coverage()` in `coverage_helpers.rs` calls `rt_coverage_decision_probe` (decision table) instead of `rt_coverage_condition_probe` (condition table). So conditions are stored as decisions, inflating decision count.
**Fix:** Call `rt_coverage_condition_probe` instead, which stores in the separate conditions table. The runtime has this function at `runtime/src/coverage.rs:379`.

### Fix 4: `bin/simple` needs release build (difficulty: 1)
**Issue:** Current `bin/simple` is a debug build (slow). Should build release for commit.
**Fix:** `cargo build --release` and copy to `bin/simple`.
