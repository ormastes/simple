# Guide A1 — make the pure-Simple test runner able to EXECUTE a child spec on a seed host

Owner: one sonnet/haiku-class agent. Follow literally. Do not exercise judgement
outside the "Decision points" section.

## Why this exists (measured 2026-09-05, do not re-derive)

Running the pure-Simple runner from source on this host —

```
SIMPLE_BINARY=/abs/src/compiler_rust/target/debug/simple \
  src/compiler_rust/target/debug/simple run src/app/test_runner_new/main.spl <dir>
```

— makes every child spec report `Error: Compilation failed: ` (empty stderr) and
`SPEC FILE VERDICT ... outcome=NOT_RUN executed=0`. Two confirmed causes:

1. `src/app/test_runner_new/test_executor_parsing.spl:55-66 find_simple_binary`
   takes `cli_get_args()[0]` as the binary. Under `simple run <script>`, argv[0]
   IS THE SCRIPT (`build/probe/argv_probe.spl` printed `argv[0]=build/probe/argv_probe.spl`).
   `file_exists(".../main.spl")` is true, so the runner tries to spawn the `.spl`
   file as an executable. `SIMPLE_BINARY` (honoured elsewhere) is never consulted
   there; `SIMPLE_RUNTIME` is consulted only AFTER argv[0].
2. With the default `TestExecutionMode.Interpreter`, `--verbose` still prints
   `[native] Compiling <spec> to <tmp>.smf` — i.e. `run_test_file_native`
   (`test_runner_execute.spl:504`) is reached, which runs
   `<binary> compile <spec> -o <smf>`. Under the seed that compile fails. The
   Interpreter arm at `test_runner_main.spl:772` should reach
   `run_test_file_interpreter` (`test_runner_execute.spl:46`), which spawns
   `<binary> run <spec>` (see `build_child_args`, `test_executor_parsing.spl:256`).
   The routing point that diverts to native has NOT been located — that is your
   first task.

## Files to touch

- `src/app/test_runner_new/test_executor_parsing.spl` — `find_simple_binary()`.
- Whichever file the `[native]` route lives in (find it; expected under
  `src/app/test_runner_new/`).
- Two new specs (testing.md: every fix ships a reproducing spec and a
  generalisation spec):
  - `test/01_unit/app/test_runner/find_simple_binary_rejects_script_argv0_spec.spl`
  - `test/01_unit/app/test_runner/find_simple_binary_env_precedence_spec.spl`

## Exact change 1 — `find_simple_binary`

Replace the argv[0] block so that a candidate is accepted ONLY if it is an
executable binary, never a source file, and so that an explicit env override
wins:

```simple
fn find_simple_binary() -> text:
    if _cached_binary_path != "":
        return _cached_binary_path
    # 1. Explicit override wins: SIMPLE_BINARY, then SIMPLE_RUNTIME.
    for key in ["SIMPLE_BINARY", "SIMPLE_RUNTIME"]:
        val configured = env_get(key) ?? ""
        if configured != "" and file_exists(configured) and not configured.ends_with(".spl"):
            _cached_binary_path = configured
            return configured
    # 2. argv[0] only when it is the running EXECUTABLE, not a script being run.
    val args = cli_get_args()
    if args.len() > 0:
        val self_exe = args[0]
        if self_exe != "" and file_exists(self_exe) and not self_exe.ends_with(".spl"):
            _cached_binary_path = self_exe
            return self_exe
    # 3. existing candidate list unchanged below
```

Keep the existing fallback candidate list exactly as it is. Do not add new
candidates.

## Exact change 2 — locate and fix the native diversion

1. Add a temporary `print "[route] mode=" + mode_to_str(effective_options.mode)`
   immediately before the `match effective_options.mode` at
   `src/app/test_runner_new/test_runner_main.spl:770`, run the reproduction
   below, read the printed mode, then DELETE the print.
2. If the printed mode is `interpreter`, the diversion is inside
   `run_test_file_interpreter` or `build_coverage_wrapper`; grep for
   `run_test_file_native(` and `"compile"` inside those and fix the branch so
   that with no `--coverage`, no `SIMPLE_MCDC_MODE`, and no `.smf` sibling the
   Interpreter arm spawns `<binary> run <spec>`.
3. If the printed mode is `smf`/`native`, find where `options.mode` was changed
   after `parse_test_args` (grep `mode =` / `mode:` in
   `src/app/test_runner_new/*.spl`) and make the default stay `Interpreter`.

Whatever you find, the acceptance `it` below decides; do not stop at "it looks
right".

## Reproduction / acceptance command

```
SIMPLE_BINARY=$PWD/src/compiler_rust/target/debug/simple \
  src/compiler_rust/target/debug/simple run \
  test/02_integration/test_runner/in_development_tag_runner_spec.spl
```

Acceptance `it`s (group (e) of that spec, both must pass):

- `executes the tagged spec's `it`, sees the real assertion failure, and still neutralises it`
- `reddens the sweep for the IDENTICAL assertion when the tag is absent (control)`

Their oracles: the tagged fixture's own `SPEC FILE VERDICT` line carries
`executed=1 failed=1`, the output carries `expected 1 to equal 2`, contains no
`Compilation failed` and no `E1034`, still prints `IN-DEVELOPMENT SKIP ... (1
expected failure(s)`, and the sweep exits 0; the untagged control exits non-zero
with `1 failed` and no skip marker.

Discard any run whose output contains `E1034` — it proves nothing.

## Decision points (the only judgement you may exercise)

- If change 2 turns out to require touching `build_coverage_wrapper`, keep
  MC/DC behaviour unchanged when `SIMPLE_MCDC_MODE` is `on`/`dynamic`; only the
  unset case may change.
- If group (e) still fails with `Compilation failed`, run the child command by
  hand (`<binary> run <fixture>`) and paste its stderr into your report; do not
  edit the spec.

## Checkbox rule

In `doc/03_plan/agent_tasks/plan_remains_completion_2026-09-05.md` tick item A1
ONLY when both `it`s above pass, and append
`— verified <command> → "<n> examples, 0 failures" for group (e), <date>` to
the checkbox line. A checkbox without that suffix is unticked.
