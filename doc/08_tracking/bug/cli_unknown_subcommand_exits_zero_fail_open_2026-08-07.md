# `bin/simple <unknown-subcommand>` prints an error and exits rc=0

**Filed:** 2026-08-07
**Severity:** medium — a fail-open in the CLI, and it silently defeats scripts
**Status:** OPEN

## Repro

```
$ bin/simple inspect
error: file not found: inspect
<usage banner>
$ echo $?
0
```

`inspect` is not a subcommand — `src/app/cli/dispatch/table.spl` contains zero
occurrences of it. Dispatch falls through to the run-a-file path, which reports
"file not found" and still exits **0**.

## Why it matters

Any wrapper, CI step or check script that invokes a subcommand which was
renamed, not yet implemented, or misspelled reads success. This is the same
fail-open family the repo has been bitten by repeatedly (see
`doc/08_tracking/bug/probe_harness_falls_through_exit_zero`-style findings and
the pre-push-guard `ERROR — nothing was checked` remedy in
`.claude/rules/vcs.md`): a command that *could not do the thing* must not exit 0.

Found while auditing whether a `simple inspect --assurance` subcommand exists
for the aerospace-hardening plan; it does not.

## Fix

Unknown-token fall-through should exit non-zero. Distinguish the two cases:
a token that is not a subcommand **and** not an existing file is a usage error
(exit 2); an existing file that fails to run keeps its current semantics.

Regression spec must assert the **exit code**, not the message — the message is
already correct today and asserting it would pass before the fix.

Tracked alongside WP-22 in
`doc/03_plan/language/assurance/aerospace_hardening_plan_2026-08-07.md`.
