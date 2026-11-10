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

## 2026-11-10 status — LIVE-FIXED (P3 library lane, work/p3-lib-20261110)

Root cause found and fixed in `src/lib/*/js/engine/`, two compounding O(n)
costs per `setTimeout` once the native tables grow:

1. `_register_native` (interpreter_object.spl) used local-alias-store-back
   pushes, deep-copying `functions` + `native_id_map` per registration; each
   node-compat timer handle registers 8 native methods → O(n) per timer.
   Now in-place pushes (all three family trees).
2. Every JS call linearly scanned `native_id_map` to detect native callees
   (interpreter_eval.spl eval_call/eval_new, interpreter_async.spl
   `_native_id_of_fn`) → O(n) per call. Now a binary search
   (`_lookup_native_id`) — the map is sorted by fn_id because registrations
   append increasing function indices. Native ids are strictly negative
   (min -1126, e.g. NATIVE_SET_TIMEOUT = -40), so 0 is the absent sentinel.

Evidence (seed-smoke, deployed seed from main repo, SIMPLE_LIB=src,
worktree work/p3-lib-20261110): the bug's exact fill loop in a standalone
`run` probe (the spec-runner closure cannot load under the Windows seed:
unknown extern GetProcessHeap — host-limit, separate seed gap). Before:
512→1024 ≈ 35 s, 1024→2048 ≈ 209 s, 4096 never finished (>280 s). After:
512 +6 s, 1024→2048 +18 s, 2048→4096 +67 s, all with denied=0.0 and
pending/handle collections exactly N. A spec-equivalent functional probe
(requestAnimationFrame + drain, 4096 fill, completedFrame.refresh() identity,
state string "1:false:false:true") prints PROBE-VERDICT PASS in ~66 s wall
including startup. The checked-in spec
test/01_unit/lib/common/completed_animation_handle_capacity_spec.spl is the
regression guard (runnable on Linux CI; Windows-seed-blocked here).
Fix cycles: 4 (dict-index variant reverted: own-field Dict index-write is
dropped by the seed interpreter, recorded here so later lanes do not retry).

## 2026-11-11 status — SUPERSEDED (P3-essential library lane, work/p3-lib3-20261111)

Verify-only row: claim was PR #8150. **Claim holds.** The fix
`bbae0fd2296d` ("fix(js): remove O(n^2) from timer-handle native
registration and per-call native dispatch") is an ancestor of this base
(merge `6dd3904ea935`; both verified via `git merge-base --is-ancestor`).
On this lane's refreshed seed (bin/simple.exe, build-commit `0791c2b7f4a7`)
the doc's exact spec command now terminates in ~8 s (load-time semantic
error below) — the recorded ">150 s, never completes" hang symptom is
objectively gone. Executed fill evidence remains the 2026-11-10 lane's
before/after probe timings on the prior deployed seed: 4096 never finished
pre-fix; post-fix full 4096 fill with denied=0, exact 4096 collection
sizes, refresh identity, state `1:false:false:true`, ~66 s wall.

Host-gap note (new observation, NOT this bug): on the 2026-11-11 refreshed
seed, the spec and any probe that pulls the common 9-variant `JsValue` into
the same compilation as `std.js.engine.runtime` die at semantic load —
`method 'trim' not found on value of type enum in nested call context`,
preceded by `warning[enum-bare-name-ambiguous]: enum JsValue is registered
again with a different variant set` (common 9-variant copy wins over the
nogc 8-variant copy; load-only `JsRuntime` construction passes, so the
failure is size-independent and cannot mask the O(n^2) symptom class). This
is the known `seed_enum_variant_bare_name_last_registration_wins_2026_10_19`
hazard surfacing on the refreshed seed; routed to the seed lane via this
lane's evidence file (`build/review/p3fix-lib3-20261111.sdn`) — do not
re-dispatch as a timer-queue regression.
