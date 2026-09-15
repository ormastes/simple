# MC/DC defaults ON, so every "interpreter" test run is diverted to native compile

**Date:** 2026-09-05
**Status:** OPEN — root cause located, fix is a policy decision, not a code bug
**Severity:** blocks the entire test runner on any host without a compiling binary

## Chain

`run_test_file_interpreter` (`src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl:194`):

```simple
val configured_mcdc_mode = env_get("SIMPLE_MCDC_MODE") ?? ""
if options.coverage or configured_mcdc_mode == "on" or configured_mcdc_mode == "dynamic":
    return run_test_file_native(file_path, options)
```

`SIMPLE_MCDC_MODE` is set to `"on"` by `propagate_env_vars` ->
`resolve_mcdc_mode_for_profile`
(`src/lib/nogc_sync_mut/test_runner/test_runner_config.spl:99-129`) whenever
there is no `--profile` and no `simple.sdn` profile section — the ordinary
case. That function's own comment states the intent: *"An unresolved/default
profile is also normal... never a way to bypass exact MC/DC."*

`run_test_file_native` then runs `<binary> compile <spec> -o <smf>`. On this
host no deployed binary can compile current source, so every child dies with
the empty `Error: Compilation failed:` and
`outcome=ERROR ... executed=1 passed=0 failed=1`.

## Why this matters beyond one host

It is the reason the `@tag:in-development` neutralisation of a FAILING
ASSERTION has never been demonstrated. The tagged fixture never executes its
assertion, so the runner only ever exercises the crash/error branch of
`classify_in_development`. The suite's green groups (a)-(c) are crash-path
artefacts, and group (d) — a tagged spec that ought to PASS — is red for the
same reason.

Direct execution is fine: `SIMPLE_EXECUTION_MODE=interpret <binary> run
<fixture>` prints the real assertion failure. The seed is not the problem;
the runner's forced diversion is.

## What is NOT the cause (two misattributions, corrected)

1. `src/app/test_runner_new/test_executor_parsing.spl` is **dead code** —
   imported by nothing (`grep` for `app.test_runner_new.test_executor_parsing`
   returns 0). The live module is
   `src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl`.
2. That live `find_simple_binary` does **not** naively take argv[0]; it
   already rejects a non-`/simple` argv[0] and canonicalises via
   `/proc/self/exe`. Its real gaps are narrower: it reads only
   `SIMPLE_RUNTIME` and never `SIMPLE_BINARY` (the variable the runner spec's
   own helper uses), and `/proc/self/exe` is a no-op on macOS.

## The decision this needs

Whether a run with no resolved profile should force MC/DC — and therefore
native compilation — is a compliance policy, documented as deliberate. It is
not a routing bug and was not changed unilaterally. The options:

- keep the default and accept that the runner cannot run on a host with no
  compiling binary;
- make the diversion conditional on a compiling binary actually being
  available, failing closed with a named verdict when it is not;
- keep MC/DC mandatory only for the lanes that claim MC/DC evidence.

## Repro

```sh
mkdir -p test/01_unit/_probe && cat > test/01_unit/_probe/wip_spec.spl <<'SPL'
# @tag:in-development
use std.spec

describe "d":
    it "fails on a real assertion":
        expect(1).to_equal(2)
SPL
src/compiler_rust/target/debug/simple run src/app/test_runner_new/main.spl test/01_unit/_probe
SIMPLE_MCDC_MODE=off src/compiler_rust/target/debug/simple run src/app/test_runner_new/main.spl test/01_unit/_probe
```

## RESOLVED as a diagnosis — Gap A demonstrated 2026-09-05 17:45

With BOTH faults bypassed the full `@tag:in-development` contract works. The
two faults are independent and either alone kills every child, which is why
single-variable experiments looked like they changed nothing:

1. `SIMPLE_MCDC_MODE=off` — bypasses the native diversion described above.
2. `SIMPLE_RUNTIME=<a binary with a `run` command>` — `find_simple_binary`
   reads `SIMPLE_RUNTIME` and **never** `SIMPLE_BINARY`, so setting
   `SIMPLE_BINARY` (what the runner's own spec helper and the guides use)
   is ignored and a bootstrap CLI gets spawned: `unknown command 'run'`.

```
SIMPLE_MCDC_MODE=off SIMPLE_RUNTIME=$PWD/src/compiler_rust/target/debug/simple \
  src/compiler_rust/target/debug/simple run src/app/test_runner_new/main.spl <dir>
```

```
Files:   3 discovered, 3 executed
IN-DEVELOPMENT SKIP            wip_failing_spec.spl (1 expected failure(s); @tag:in-development)
IN-DEVELOPMENT UNEXPECTED PASS wip_passing_spec.spl (1 example(s) passed) — ready to promote
SPEC FILE VERDICT plain_ok_spec.spl    outcome=OK executed=1 passed=1 failed=0
Results: 2 total, 2 passed, 0 failed, 1 skipped
In-development: 1 skipped (expected to fail), 1 UNEXPECTED PASS (ready to promote)
```

**Why this is proof and the earlier greens were not.** The `UNEXPECTED PASS`
branch cannot be reached through the crash path: a file that never executes
has nothing to pass. Its appearance, alongside a genuinely-failing tagged
file being neutralised and an untagged control passing, exercises all three
classification outcomes in one sweep. Every earlier "green" in this lane came
from `classify_in_development`'s error branch with `executed=0`.

`outcome=NOT_RUN` on the neutralised file remains the documented cosmetic
limitation (a neutralised file is left `passed=0, failed=0, skipped=1`, so
the verdict line sees `0,0`); it does not affect the exit code.

**What is still open is the DEFAULT, not the mechanism.** Out of the box
(no profile, no `SIMPLE_RUNTIME`) both faults fire and the runner cannot
execute anything on a host without a compiling binary. Fault 2 is a plain
bug — `find_simple_binary` should also read `SIMPLE_BINARY`. Fault 1 is the
policy decision recorded above.

**Caution for whoever re-runs this:** create the fixtures in a SEPARATE
command from the sweep. A first attempt wrote `wip_passing_spec.spl` in the
same command and the runner reported `Results: 1 total` — the file was never
discovered, and the absent `UNEXPECTED PASS` line looked like a negative
result rather than a test that never ran.

## Fault 2 FIXED in source 2026-09-05

`find_simple_binary` (`src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl`)
now reads **both** `SIMPLE_BINARY` and `SIMPLE_RUNTIME`, preferring the
former. Previously only `SIMPLE_RUNTIME` was consulted, so an explicit
`SIMPLE_BINARY` — the name the runner's own integration-spec helper
(`simple_binary()`) and every agent guide uses — was silently ignored and
resolution fell through to the deployed `bin/simple`, a BOOTSTRAP cli with
no `run` command. Every child then died with `error: unknown command 'run'`.

Verified with `SIMPLE_BINARY` alone (no `SIMPLE_RUNTIME` set):

```
IN-DEVELOPMENT SKIP            wip_failing_spec.spl (1 expected failure(s); @tag:in-development)
IN-DEVELOPMENT UNEXPECTED PASS wip_passing_spec.spl (1 example(s) passed) — ready to promote
Files:   3 discovered, 3 executed
Results: 2 total, 2 passed, 0 failed, 1 skipped
In-development: 1 skipped (expected to fail), 1 UNEXPECTED PASS (ready to promote)
```

**Fault 1 remains open and is the only thing between this and working by
default**: with MC/DC left at its default `on`, the same command still
diverts to `run_test_file_native` and fails to compile. `SIMPLE_MCDC_MODE=off`
is still required. That is the policy decision recorded above, deliberately
not taken here.
