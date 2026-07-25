# `*_log_modes_spec.spl`: nested `bin/simple run <app>/main.spl` subprocess returns empty stdout under `bin/simple test`, but the identical command succeeds run standalone

**Date:** 2026-07-20
**Component:** `bin/simple test` execution of specs that spawn
`rt_process_run("/bin/sh", ["-c", "... bin/simple run <app>/main.spl <args>"])`
**Severity:** High — affects the entire `*_log_modes_spec.spl` family (each
app's CLI `--log-mode`/`--help`/`--progress` contract test)
**Found by:** whole-suite triage campaign, `test/02_integration/app/`
cluster; confirmed via individual re-run (`timeout 90` and `timeout 180`,
`--no-session-daemon`) and via manual standalone reproduction

## Symptom

Specs of the shape:

```simple
fn _run_<app>(args: [text]) -> (text, text, i64):
    val joined = args.join(" ")
    rt_process_run("/bin/sh", [
        "-c",
        "REPO=$(pwd); SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/<app>/main.spl\" " + joined
    ])
```

fail every example with `expected  to contain <expected-substring>` — i.e.
`out` is completely empty — even for the simplest case (`--help`).

Confirmed NOT a general regression in the target app's CLI: running the
exact same command manually, outside the test harness, in a plain shell
succeeds and prints correct output, e.g.:

```sh
cd /home/ormastes/dev/pub/simple
REPO=$(pwd); SIMPLE_LIB="$REPO/src" "$REPO/bin/simple" run "$REPO/src/app/plugin/main.spl" --help
# prints real help text, exit 0
```

but re-running `plugin_log_modes_spec.spl` under `bin/simple test` (twice,
to rule out flakiness) deterministically fails all `--help`/
`--log-mode=json`/`--progress=dot` examples with empty `out`.

## Confirmed affected specs

- `test/02_integration/app/plugin_log_modes_spec.spl` — 3 of 4 examples
  (`shows shared log options in help`, `supports log-mode json for empty
  plugin list`, `supports dot progress for empty plugin list`); reproduced
  twice, deterministic, ~55s duration each run
- `test/02_integration/app/cli_log_modes_spec.spl` — 5 of 5 examples fail
  the same way (re-run at `timeout 180`, completes in ~74s, not a timeout)

Both target apps (`plugin/main.spl`, `cli/main.spl` → re-exports
`app.cli._CliMain.main_and_help`) have real, substantial CLI implementations
(not stubs — see `dashboard_cli_stub_no_log_mode_support_2026-07-20.md` for
the one confirmed stub case, which is a different root cause).

## A basic subprocess+stdout-capture sanity check passes

To rule out `rt_process_run`/stdout-capture being broadly broken under
`test`, this was verified to work fine:

```simple
val (out, err, code) = rt_process_run("/bin/sh", ["-c", "pwd; echo OUT_END; echo ERRTEXT 1>&2"])
expect(out).to_contain("OUT_END")   # PASSES under `bin/simple test`
```

So the defect is specific to the nested command being a **heavy**
`bin/simple run <big-app>` invocation (large transitive `use` graph,
multi-second compile even standalone), not to `rt_process_run` mechanics in
general.

## Root-cause hypothesis

Not confirmed from source. Leading candidate: spawning a second, resource-
heavy `bin/simple run` compile-and-execute as a child of an
already-resource-heavy `bin/simple test` process (same seed binary,
`bin/release/x86_64-unknown-linux-gnu/simple`, known to print its own
"bootstrap seed only" memory/perf warning) causes the child to silently fail
or be starved — possibly OOM, possibly an internal soft-timeout in the
child compile path — without any error text landing in the captured `out`/
`err` (which the spec doesn't assert on, but should be checked here in any
follow-up: is `err` also empty, or does it carry a diagnostable message?).
Also plausibly related to (but not confirmed to be the same as) the
resource-contention timeout family the campaign guide describes for the
sibling `app_root_log_modes_spec.spl` (that one instead surfaces as
`expected 143 to equal 0` — an explicit SIGTERM exit code on the nested
process — which is consistent with the same underlying contention, just a
different observable symptom).

## Note

Both spec files are correct as written (they reflect real, working CLI
contracts, confirmed by manual reproduction) and were left unmodified.
