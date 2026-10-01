# JS timer/animation-frame queue hangs (>150s, never completes) at 4096 entries

Date: 2026-09-01
Status: OPEN
Severity: Medium — test hang, likely O(n) or worse per-op cost in the
JS-engine timer/task queue implementation

## Evidence

```bash
timeout 150 bin/simple.exe test test/01_unit/lib/common/completed_animation_handle_capacity_spec.spl
```

```
error: test-runner: TERMINATED: child died by signal with no crash sentinel and no fault diagnostic
SPEC FILE VERDICT: ... declared>=1 executed=0 passed=0 failed=1 dropped=1 unrun=1 reason=child-died-by-signal
Results: 0 total, 0 passed, 0 failed
```

`real 2m30.382s` (150s wall timeout hit; the process was still running when
killed — this is not a fast failure, the run genuinely never reaches the
`Results:` line).

Isolated with a 30s timeout first (also killed before completion), then
retried at 150s to rule out "just slow" — still killed. The spec
(`test/01_unit/lib/common/completed_animation_handle_capacity_spec.spl:26-30`)
does:

```simple
step("Fill the canonical timer and animation task queue")
match runtime.eval(
    "var denied = 0; for (var i = 0; i < 4096; i = i + 1) {" +
    " if (setTimeout(function() {}, 1000) === undefined) {" +
    " denied = denied + 1; } } denied"
):
```

i.e. 4096 `setTimeout` calls into the JS engine's timer/task queue
(`runtime.interpreter.pending_timer_tasks` / `timer_handle_ids` /
`timer_handle_object_ids`, per the assertions immediately after that
expect these to reach exactly 4096 entries).

## Impact

This spec never completes within the harness's default watchdog (or even a
generously extended one), which will always read as a hang/timeout rather
than a genuine pass or fail, and blocks any batch/directory `bin/simple test`
run that includes it — a single such file can turn `Requested N spec
file(s); executed N` into a wedged process needing an external kill.

## Root cause (not investigated)

Not narrowed to a specific function — flagging the SYMPTOM (4096-entry timer
queue fill hangs) per CLAUDE.md's COW-alias-hotpath guidance: "Simple's value
semantics are copy-on-write... `.push()` on a collection reached through
certain patterns deep-copies the WHOLE collection per write — O(n) per
operation, invisible on small fixtures, catastrophic at real scale." A
4096-iteration loop that pushes into `pending_timer_tasks`/`timer_handle_ids`/
`timer_handle_object_ids` on every iteration is exactly the shape that class
of bug hits (O(n) per push -> O(n^2) total -> ~16M copy-steps by the last
iteration). Not confirmed by profiling — this needs
`sh scripts/check/check-cow-alias-hotpath.shs` or a direct read of the JS
engine's timer-registration code path (likely under
`src/lib/**/js/engine/**`) to confirm before attempting a fix.

## Not fixed here

Per `.claude/rules/testing.md`, this spec is left RED/hanging rather than
skipped, tagged in-development, or deleted. Not modified.
