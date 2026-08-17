# `check-native-trailing-default-param.shs` fails at `Widget.stat(2)` — MIR lowering error: undefined variable Widget

- **Filed:** 2026-08-17
- **Status:** OPEN
- **Severity:** P1 — blocks pushes for every lane (guard is on the pre-push roster)
- **Class:** MIR lowering of a static/associated method call on a class name
- **Prior row (same guard, different diagnosis):**
  `doc/08_tracking/bug/native_trailing_default_param_guard_red_at_origin_tip_2026-08-15.md`
  attributed the red to an environmental/native-build-worker cause and recorded
  only the truncated `native-build worker exited with code 1`. This row records
  the concrete lowering error now visible in the guard output. That row is left
  untouched; it is not edited here.

## Summary

`sh scripts/check/check-native-trailing-default-param.shs` is RED on
`origin/main`. Verdict and the underlying compiler error, verbatim, as
reproduced and reported by the task owner (not re-run by the author of this
row):

    FAIL — native-build failed to compile the fixture (exit 1, log saved to /tmp/check-native-trailing-default-param.last.log)
    error: MIR lowering error: undefined variable Widget

The guard compiles one self-contained fixture,
`test/fixtures/native_trailing_default_param/main.spl`.

## Localisation within the fixture (reported measurement)

| fixture line | construct | result |
|---|---|---|
| 27 | `class Widget:` | declares the class |
| 52 | `var w = Widget(base: 100)` | **lowers fine** — constructor shape works |
| 56 | `Widget.stat(2)` | **FAILS** — `undefined variable Widget` |

So the class itself resolves for construction; only the static/associated
method call form on the bare class name fails.

## Root cause — RESOLVED 2026-08-17, superseding the original hypothesis

The row was filed with a hypothesis that MIR lowering resolved the receiver
`Widget` as a **variable reference** rather than a type name. **That hypothesis
was wrong.** The real cause, found by a concurrent session and read directly
from the source:

`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` guarded its
static-method recovery path with

    if static_method_id == nil and static_receiver_kind_disc < 0:

which assumes `rt_enum_discriminant` returns a **negative sentinel** on failure.
Under native-build it does not — it returns garbage **positive** values (a
measured example: `1337030607`). The guard therefore never fired and the entire
static-method recovery branch was **dead code**, so a static call fell through
to variable lookup and reported `undefined variable Widget`.

The landed fix widens the guard to also accept an empty receiver name:

    if static_method_id == nil and (static_receiver_kind_disc < 0 or static_receiver_name == ""):

now at `method_calls_literals.spl:2705`.

This is the same defect family as `access.rs:288`'s `.unwrap_or(0)` and
`TestRunResult::success()`: **a sentinel that is not actually a sentinel**, read
as a valid value, producing a silent wrong result rather than an error. When an
`rt_*` accessor's failure mode is not contractually specified, do not infer one
from a plausible convention — check the value's validity directly.

The measured facts in the rows above stand unchanged; only the explanation
changed.

## Misdiagnosis correction — read this before patching anything

A circulating notice claimed this guard is RED because
`src/compiler/50.mir/verification_semantic_coverage.spl` (landed by
`d9dfcbf80e0`, SHA quoted from the notice, not independently confirmed here)
"does not parse: expected pattern, found Indent". **That is wrong on two
independently measured counts:**

1. `bin/simple lint` on `src/compiler/50.mir/verification_semantic_coverage.spl`
   reports `Found 0 error(s), 3 warning(s)`, rc=0. The file parses.
2. The guard's full output mentions `verification_semantic_coverage`
   **zero** times. The guard builds one self-contained fixture and never reads
   that file.

**Do not patch `verification_semantic_coverage.spl` for this guard.** It is not
in the failure path, and a "fix" there will change a file that is not broken
while leaving the guard red.

## Impact

The guard is wired into the pre-push roster at
`scripts/check/pre-push-conflict-tree-guard.shs:208` (line as reported), so
while it is red it blocks pushes for every lane.

## Unblock

Fix the lowering of a static/associated method call whose receiver is a class
name, so `Widget.stat(2)` compiles under the native-build lane, then re-run
`sh scripts/check/check-native-trailing-default-param.shs` and expect a PASS
verdict line.

## Not yet established

- Whether the guard is now fully green: at last measurement it still FAILed,
  but with neither `undefined variable Widget` nor the parse error present, so
  at least one further independent cause remains unidentified.
- Whether the interpreter lane has the same defect — the prior row notes the
  interpreter pass of this fixture printed the expected output, which suggests
  the defect is native-lane-specific, but that was measured before this error
  text was visible and has not been re-checked.
- Whether any other in-tree code hits the same shape (no census was run).
