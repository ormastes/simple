# Bug: add_remove_log_modes_spec.spl Timeout Under Resource Limits

**Date:** 2026-07-17 / 2026-07-18 (diagnosis update)
**Lane:** L5 (test/02_integration and test/integration)  
Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

## Root Cause (Confirmed)
Spec invokes `bin/simple run` with `SIMPLE_LIB="$REPO/src"`, which forces the interpreter to load ALL 600+ .spl files from:
- src/lib/ (~200+ files across async/sync/gc tiers)
- src/compiler/ (~150+ files)
- src/app/ (~80+ files including all app implementations)
- src/runtime/, src/i18n/ (additional overhead)

Each test case spawns a fresh interpreter process, triggering full module resolution. At interpreter scale, parsing + resolving 600+ files takes >90s per invocation under test runner resource governor (120s limit).

**Symptoms witnessed:**
- Interpreter emits: `[memory-guard] SIMPLE_LIB=... contains 600+ .spl files — consider narrowing scope`
- Consistent 120+ second hang per test file
- No error/exception logged; resource limiter forcibly kills process at timeout

**Why spec couldn't remove SIMPLE_LIB:**
- Apps use `use std.cli`, `use std.log`, `use app.io`
- Without SIMPLE_LIB, module resolver fails: "unknown extern function rt_cli_arg_count"
- With SIMPLE_LIB=src: 600+ file load kills timeout
- With SIMPLE_LIB narrowed: complex rebuild of module tree (see doc/07_guide/app/editor_tui.md § narrowing approach)

## Current Status: INCONCLUSIVE FIX
Spec remains at original form (SIMPLE_LIB="$REPO/src"). Removal breaks module resolution; narrowing requires 3-layer directory copy overhead that negates savings.

## Recommended Solutions

**Option A (Preferred): Use compiled app binaries**
- Compile add/remove apps to binaries: `bin/release/add`, `bin/release/remove`
- Test calls binaries directly (no interpreter overhead)
- Matches production deployment model

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

## Verification 2026-08-17 (content classification, fleet lane I)
STILL-OPEN and still UNSETTLED — this doc`s own status ("INCONCLUSIVE FIX") is
the accurate one, and this lane could not upgrade it.
Content check: `test/02_integration/app/add_remove_log_modes_spec.spl` is
present and still carries a `SIMPLE_LIB`/`SIMPLE_TIMEOUT_SECONDS` reference,
i.e. the SIMPLE_LIB=src whole-tree interpreter load this doc blames is still the
shape of the test.
Why every timing number in this doc must be re-taken, not trusted:
`SIMPLE_TIMEOUT_SECONDS` was **parsed and then discarded** until recently, and
even after that it misbehaved (a value of 600 truncated a run at 135s, while 0
let it finish). Any conclusion in this doc that rests on that variable proves
nothing about the real runtime. Re-measurement must use an explicit
`--timeout <n>` flag.
NOT PROVEN HERE: no re-run. A stage-3 self-hosting bootstrap held this host at
~98% CPU for the whole session; the shared test slot never freed. A timeout row
measured under that contention would be pure noise in the failing direction,
which is worse than no measurement. Needs an idle host.
