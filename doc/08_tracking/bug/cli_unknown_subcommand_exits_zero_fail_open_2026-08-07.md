# `bin/simple <unknown-subcommand>` prints an error and exits rc=0

**Filed:** 2026-08-07
**Severity:** medium — a fail-open in the CLI, and it silently defeats scripts
**Status:** NOT A BUG / RESOLVED — re-verified 2026-08-17.

## Re-verification 2026-08-17 (partial-fix sweep, lane 1)

```
$ bin/simple definitely-not-a-command >/dev/null 2>&1
$ echo $?
1
```

An unknown subcommand exits **1**, not 0. The CLI does not fail open. This
matches the earlier "did NOT reproduce" measurement rather than the original
filing, on a second independent probe ~10 days later. Closing.

NOT PROVED: only the deployed Rust seed was probed, and only with a single
unknown-subcommand shape.

--- original filing below, kept for history ---

**Status (original):** PARTIAL — the filed rc=0 claim did NOT reproduce (measured rc=1
from the deployed seed across 7 token shapes, see "Corrected measurement").
The pure-Simple dispatch fall-through (`app.cli.main`) now returns exit 2 for
this case, verified at the function level; **unverifiable at the
`bin/simple <token>` process boundary** until a self-hosted binary is
deployed. The Rust seed (`main.rs`) already returns 1 for this case and was
left untouched, out of scope by repo rule.

Title records the original filed claim ("exits_zero_fail_open"); that repro
did not reproduce on re-measurement — see "Corrected measurement" below.

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

## Corrected measurement (WP-22 close-out, 2026-08-07)

Re-running the repro against the currently deployed `bin/simple`
(`bin/release/x86_64-unknown-linux-gnu/simple`, the Rust bootstrap seed — no
self-hosted `bin/release/linux-x86_64/simple` is deployed today) gives:

```
$ bin/simple inspect; echo $?
error: file not found: inspect
<usage banner>
1
```

**`$?` is 1, not 0**, taken directly off the command (never through a pipe,
per `.claude/rules/testing.md`). A sweep of related fall-through shapes
(`inspect --assurance`, `--assurance`, `-inspect`, a directory `src`, a
non-`.spl` existing file `README.md`, nested `verify inspect`) also found no
rc=0 case. The lowercase `error:` text traces to
`src/compiler_rust/driver/src/main.rs:1674`, which has read `return 1` since
the line was introduced (`git log -S` shows one commit, already `return 1`) —
this seed path was never observed at rc=0. The original rc=0 repro most
likely came from a `$?`-through-a-pipe or stale-binary artifact of exactly
the kind this repo has been bitten by before (see
`.claude/rules/testing.md` binary-identity and pipe-`$?` caveats).

**Scope note:** per repo rule, only the pure-Simple layer was fixed, not the
Rust seed (`src/compiler_rust/driver/src/main.rs` was left untouched). The
Rust seed's `handle_file_execution` already returns 1 for this case and is
out of scope. The self-hosted pure-Simple entry (`app.cli.main`, backed by
`src/app/cli/_CliMain/main_and_help.spl`) is where this WP lives, but no
built self-hosted binary is currently deployed, so the corrected rc=2
behavior cannot be demonstrated at the `bin/simple <token>` process boundary
today — only at the function level (see below). Re-verify at the process
boundary once a self-hosted `bin/simple` is deployed.

### What changed

`src/app/cli/_CliMain/main_and_help.spl`, dispatch fall-through (`main()`'s
final `else`, reached when `first` matches no known subcommand string and
`cli_file_exists(first)` is false): now returns
`cli_dispatch_fallthrough_exit_code(first)` — a new function that returns
`CLI_USAGE_ERROR_EXIT_CODE` (2) for this usage-error case, distinct from the
1 an existing-but-failing file execution can still return via
`cli_run_file(...)` on the sibling branch (unchanged). Previously this branch
returned a flat `1`, indistinguishable from a file-execution failure.

The `-1` sentinel `cli_dispatch_fallthrough_exit_code` returns for an
existing-file token is an internal signal to the caller ("run the file
instead"); it is unreachable from `main()`'s actual return path, since the
caller's `elif cli_file_exists(first):` branch handles that case before the
`else` (which calls this function) can ever be reached — `main()` never
returns `-1` as a process exit code.

Regression spec:
`test/01_unit/app/cli/cli_unknown_subcommand_exit_code_spec.spl` — asserts
`cli_dispatch_fallthrough_exit_code("inspect") == 2` (exit code, not
message), a near-miss token (`"built"`), and the non-regression that an
existing file (`"src/app/main.spl"`) does NOT get the usage-error code.

Measured both ways by editing `CLI_USAGE_ERROR_EXIT_CODE` in place and
restoring it (not committed, scratch-only):
- RED (constant temporarily set to `1`, i.e. pre-fix behavior):
  `Results: 4 total, 1 passed, 3 failed`
- GREEN (constant restored to `2`, the landed fix):
  `Results: 4 total, 4 passed, 0 failed`

### Other fail-open-shaped paths found, left out of scope

- `dispatch.spl:102-109` (`app.cli.dispatch.dispatch_to_rust`): a table entry
  with no Simple implementation returns 1 via `dispatch_to_rust`. This is a
  *known* subcommand missing its implementation, a different case from an
  *unknown* token; left alone, but flagged for a future WP if it should also
  distinguish usage errors.
- `main_and_help.spl:537` (existing-file branch): returns
  `cli_run_file(...)` unwrapped. `try_simple_app`'s own doc comment in
  `dispatch.spl` states `cli_run_file` returns **negative** values on
  load/parse failure — if a negative code reaches the process exit boundary
  un-clamped it could produce a nonsensical or platform-dependent exit status
  (shells mask exit codes to 8 bits). Not exercised by this WP; worth a
  follow-up measurement.
- `bin/simple test inspect` hung and had to be killed (rc=143, SIGTERM) in
  the sweep above rather than returning any code — a separate defect
  (test-runner treats `inspect` as a filter/path argument and appears to loop
  or block rather than reporting "no tests matched"). Not investigated
  further here; flagging for a dedicated bug report if not already tracked.
