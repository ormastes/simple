# `exp run` delegation loses the nested `run` argument under `simple run`

Status: confirmed genuine product bug (CLI argument-forwarding gap on the
`simple run` dispatcher). `exp run <script>` can never reach the app's `run`
handler when launched as `simple run src/app/exp/main.spl run <script>`.

## Evidence

`exp ls`, `exp gc`, and `exp run` (no script, prints `error: script required`)
all dispatch correctly, so subcommand parsing inside the app is fine. But:

```
simple run src/app/exp/main.spl run /tmp/exp_probe.spl
```

prints the exp usage banner and exits 0 instead of executing the script.
Instrumenting `src/app/exp/main.spl` (`print` of `get_cli_args()` right after
the call) shows `raw_args=[]` — the child receives **no** arguments for the
`run <script>` form, while `exp foo bar` yields `[foo, bar]` and `exp ls`
yields `[ls]`.

`std.cli.cli_util.get_cli_args` skips `args[1]=="run"` plus a `.spl` path, but
when the outer invocation is `simple run <prog>.spl run <script>`, the second
literal `run` and/or the trailing script is consumed by the dispatcher, so the
program observes an empty argv and falls into the usage/help branch
(`print_help_with_progress`, whose progress label is the literal `usage`, which
is what the failing spec scenario captured as `usage: 0/1 (0%)`).

A secondary defect: `cmd_run` spawns the child through a raw
`extern fn rt_process_run("./bin/simple", ...)` — a POSIX relative path with no
`.exe` — which is the exact pattern the direct-env-runtime guard forbids and
which cannot spawn on native Windows. Switching to an absolute
`bin/simple.exe` path alone did **not** restore delegation because the argv is
already empty by the time `cmd_run` would run.

## Cause and scope

Two stacked issues: (1) the `simple run <prog> <args>` dispatcher drops a
leading literal `run` (and its following script) instead of forwarding it to
`<prog>`, which affects any CLI whose first subcommand is `run`; (2) `exp`'s
delegation uses a raw FFI process spawn with a POSIX-only relative binary path.
Fixing (1) touches `get_cli_args` / the `simple` run-dispatch path shared by
every CLI app, so it is not bounded for this lane; fixing (2) alone is
insufficient.

## Correctness gate for a repair

1. Add a focused dispatcher regression: `simple run <prog>.spl run <script>`
   must deliver `[run, <script>]` to `<prog>`'s `get_cli_args()`, and
   `simple run <prog>.spl ls` must keep delivering `[ls]`.
2. Route `exp`'s child spawn through the host-portable process facade (repo
   root from `cwd`, `bin/simple.exe` on Windows) rather than raw
   `rt_process_run`, per the direct-env-runtime guard.
3. Re-run `test/02_integration/app/exp_log_modes_spec.spl`; the
   "delegates experiment script execution" scenario must print the fixture
   script's `exp-run-ok` and exit 0.
