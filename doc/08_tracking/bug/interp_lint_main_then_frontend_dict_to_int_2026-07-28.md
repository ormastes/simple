# Executing lint-main then the frontend in one interpreter session fails with "cannot convert dict to int"

- **Filed:** 2026-07-28
- **Severity:** medium — deterministic false-red for any spec combining the two graphs
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
- **Found via:** SE1 `safety-enforce` lane spec (12th example failed while 11 passed)

## Symptom

In a single `bin/simple test` interpreter session, calling anything that
executes `compiler.tools.lint.main`'s module graph (one bare
`parse_lint_profile("critical")` is sufficient) and THEN driving
`parse_full_frontend → HirLowering.lower_module → safetychecker_check_module`
fails the frontend call with:

```
error: semantic: type mismatch: cannot convert dict to int
```

## Minimal A/B (all run 2026-07-28, all deterministic)

| variant | result |
|---|---|
| fixture alone (frontend graph only) | PASS |
| fixture + lint-main **imported** but never called | PASS |
| `parse_lint_profile("critical")` executed, then fixture | **FAIL** dict-to-int |

So import is harmless; **execution** of lint-main's module init poisons the
later frontend run. No env vars, no `driver_safety_severity`, no enum compare
needed — the narrowed repro is two `it` blocks:

```simple
it "calls parse_lint_profile first":
    expect(parse_lint_profile("critical").is_some()).to_equal(true)

it "then any parse_full_frontend fixture":
    ...  # fails: semantic: cannot convert dict to int
```

(Also note: running the repro OUTSIDE `test/` fails differently —
`Cannot resolve module: std.spec` — the documented test-path landmine. Two
early probe runs were invalidated by this; put repros under `test/`.)

## Likely family

Interpreter cross-module state: the flat function/type registry lets one
module's same-named symbol hijack another's (documented family:
`feedback_interp_struct_name_collision_global_registry`,
interp `env_get` name-collision). lint-main's `config_and_model.spl` holds
module-level `Dict` state (`_DEPRECATED_PROFILE_ALIAS_WARN_COUNTS`, the
per-profile `levels` dicts); once its graph is live, some same-named symbol
resolves to a dict where the frontend expects an int. The exact colliding
symbol is not yet identified — the repro above is small enough to bisect by
commenting out lint-main globals.

## Impact

Any spec that both exercises profile plumbing AND compiles source through the
real frontend will go red on the frontend half. SE1's severity spec hit
exactly this: 11 pure-mapping/env examples green, the one real-frontend
fixture red. Worked around by keeping the two graphs in separate spec files —
the fixture assertion lives (verbatim, green) in
`test/01_unit/compiler/semantics/safety_checker_unsafe_boundary_spec.spl`.

## Guard

`test/01_unit/tmp_se1_probe/` variants reproduced this; a permanent regression
spec should assert the combined session works once fixed (two `it` blocks as
above, expecting BOTH green).

## Related

- `reference_interpreter_dict_and_value_quirks` — interpreter Dict misbehavior
- `doc/08_tracking/bug/run_vs_test_harness_divergence_2026-07-28.md` — engine-specific silent divergence family

## ALREADY_FIXED — verified 2026-08-17 (P2 triage, compiler lane)

Reproduce-first re-run of the recorded reproducer at HEAD:

```
$ bin/simple test test/01_unit/compiler/semantics/safety_checker_unsafe_boundary_spec.spl
Results: 5 total, 5 passed, 0 failed          # rc=0
```

The `cannot convert dict to int` failure in a combined lint-main-then-frontend
interpreter session does not reproduce. Closing as already fixed; no source
change was made by this lane.
