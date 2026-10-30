# test_runner_new_log_modes_spec pins a planner CLI that no longer exists (2026-10-30)

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

All of these fail the same way. In a git worktree, `$REPO/bin/simple` does not
exist, so every example fails earlier with exit 127.

## Cause

The surface under test was a startup-light planner in
`src/app/test_runner_new/main.spl`. It parsed the shared log options
(`std.nogc_async_mut.cli.log_modes.parse_log_options` / `render_progress`)
and printed a plan without running any tests. Commit `e9da588ee61`
("repair 1136 unparseable .spl files from the share-history merge") restored
the origin `main.spl`, which is the real runner entry
(`run_test_cli`). That commit removed the planner. The planner was branch-only
and never reached the current runner:

- `test_runner_args.parse_test_args` has no `--log-mode`, `--progress` or
  `--help`. `--help` is rejected as `unknown option: --help`.
- JSON output exists as `--format=json` (`test_runner_args.spl:166`), with a
  different shape.

## Why not just restore it

If the old planner returned in `main.spl`, `--log-mode=json` would switch the
real runner into a plan-only mode that never executes tests. That would invent
CLI semantics on the production entry point. The intended surface is an owner
decision:

1. Implement shared `--log-mode` / `--progress` / `--help` on the real runner
   (`test_runner_args.spl`), then rewrite the planning examples against real
   runner output. Or:
2. Retire this spec in favour of the `--format=json` contract.

The examples are not marked pending. Under the seed, a runtime `pending()`
inside an `it` body counts as passed, which would hide the gap.

## Related real gaps

- `simple run src/app/test_runner_new/main.spl --help` reports
  `unknown option: --help`.
- The spec hard-codes `$REPO/bin/simple` instead of honouring `SIMPLE_BINARY`,
  which `test_runner_child_exec_spec` honours. That makes it unrunnable in
  worktrees.
