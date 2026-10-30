# test_runner_new_log_modes_spec pins a planner CLI retired in June (2026-10-30)

Status: OPEN. The spec stays RED; an owner decision is needed.

## Symptom

`test/02_integration/app/test_runner_new_log_modes_spec.spl` fails 0/7. It runs
`$REPO/bin/simple run $REPO/src/app/test_runner_new/main.spl <args>` and expects:

- `--help` to list `--log-mode` and `--progress`;
- `--log-mode=json` with no target to print
  `{"command":"test-runner-new","status":"planned","target":"test",...}`;
- `--mode`/`--coverage`/compile-shorthand planning JSON;
- `--progress=dot` before the help text;
- `--log-mode=bogus` to exit 1;
- `Unknown test runner option: --surprise` as JSON.

Observed with the shared seed (`bin/simple` present):

```
[MEM] START: (could not read /proc/meminfo)
Error: unknown option: --help
```

All of these fail the same way. `run_test_cli` prints `Error: ...` and returns
2, so even the exit-1 example fails. In a git worktree, `$REPO/bin/simple`
does not exist, so every example fails earlier with exit 127.

## Cause

The surface under test was a startup-light planner in
`src/app/test_runner_new/main.spl`. It parsed the shared log options
(`use std.cli.log_modes`: `parse_log_options` / `render_progress`) and printed
a plan without running any tests.

`34c8e300340` ("fix(tooling): enforce pure simple test daemon dispatch",
2026-06-27) deliberately removed the planner from mainline. It replaced
`main.spl` with the real runner entry (`run_test_cli` from
`test_runner_main`) and did not touch this spec. Later, `e9da588ee61`
(2026-08-27 merge repair) only restored that post-`34c8e300340` file over a
stale branch copy. `4315a16e60d` (2026-08-21) modernized the spec while it was
already red.

The current runner has none of the pinned surface:

- `test_runner_args.parse_test_args` has no `--log-mode`, `--progress` or
  `--help`. An unknown flag returns `unknown option: {arg}`.
- JSON output is retired. `--format=json` is rejected with "JSON test output
  is retired; use --format sdn" (`test_runner_args.spl:166-167`, `242-245`).
  The live machine-readable contract is `--format=sdn`.
- The shared `std.cli.log_modes` options are used by about 15 other
  `src/app/*/main.spl` entries. `test_runner_new` is now the outlier.

## Why not just restore it

If the old planner returned in `main.spl`, `--log-mode` would switch the
production runner into a plan-only mode that never executes tests. That would
reverse `34c8e300340`. The intended surface is an owner decision:

1. Adopt the shared `--log-mode` / `--progress` / `--help` options on the real
   runner (`test_runner_args.spl`). Then rewrite the planning examples against
   real runner output, using `--format=sdn`, not JSON. Or:
2. Retire this spec, which drops the `REQ-TEST-RUNNER-LOGMODE-001` pin, and
   rely on the `--format=sdn` contract.

The examples are not marked pending. Under the seed, a runtime `pending()`
inside an `it` body counts as passed, which would hide the gap.

## Related real gaps

- `simple run src/app/test_runner_new/main.spl --help` reports
  `unknown option: --help`.
- The spec hard-codes `$REPO/bin/simple` instead of honouring `SIMPLE_BINARY`,
  which `test_runner_child_exec_spec` honours. That makes it unrunnable in
  worktrees.
