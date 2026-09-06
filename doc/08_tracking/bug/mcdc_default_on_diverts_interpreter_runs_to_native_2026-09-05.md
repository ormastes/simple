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
