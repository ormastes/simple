# Three env-var names for "which binary runs specs" produced a silent, confident, WRONG verdict

## Symptom

A gate invoked with `SIMPLE_BINARY=<path-to-good-binary>` silently ran under the
default `bin/simple` (a bootstrap CLI with no `run` command) and reported
`FAIL — ... 40 failed to load/run` with `0 neutralised as genuine assertion
failures`. That verdict was an artifact of resolving the wrong binary, not a
real result, and read as a suite-wide failure.

## Root cause

Three different environment variable names decide "which Simple binary should
execute a spec", and until 2026-09-06 each surface honoured only one or two of
them:

- `SIMPLE_RUNTIME` -- read by `find_simple_binary` in
  `src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl` (historical).
- `SIMPLE_BINARY` -- what `std.spec.engine_probe.simple_binary()` and every
  agent guide set. Silently ignored by `find_simple_binary` until 2026-09-05.
- `PLAN_ACCEPTANCE_RUNNER` -- read by
  `scripts/check/check-plan-acceptance-swept.shs`. Not honoured by either of
  the two Simple-side surfaces above until 2026-09-06.

A second, compounding fault: even once the right binary is *named*, a
resolved binary that cannot do what is asked (e.g. the deployed bootstrap CLI
answering `run` with `unknown command 'run'`) was never distinguished from a
genuine per-spec failure -- every spec spawned through it just reported
"failed to load", indistinguishable from real defects.

## Fix (2026-09-06)

1. All three surfaces now accept all three names, in this documented
   precedence order: an explicit CLI/API override (argv[0] compiled-binary
   check, or `--runner`) > `SIMPLE_BINARY` > `SIMPLE_RUNTIME` >
   `PLAN_ACCEPTANCE_RUNNER` > `/proc/self/exe` (Simple-side only) > default
   candidate search.
   - `src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl`
     `find_simple_binary()` -- added `PLAN_ACCEPTANCE_RUNNER`.
   - `src/lib/nogc_sync_mut/spec/engine_probe.spl` `simple_binary()` -- added
     `SIMPLE_RUNTIME` and `PLAN_ACCEPTANCE_RUNNER`.
   - `scripts/check/check-plan-acceptance-swept.shs` -- `RUNNER` now falls
     back through `SIMPLE_BINARY` and `SIMPLE_RUNTIME` when
     `PLAN_ACCEPTANCE_RUNNER` and `--runner` are unset.
2. The resolved binary and the mechanism that resolved it are now visible:
   - `find_simple_binary_source()` (new, exported alongside
     `find_simple_binary`) reports which of argv[0] / `SIMPLE_BINARY` /
     `SIMPLE_RUNTIME` / `PLAN_ACCEPTANCE_RUNNER` / `/proc/self/exe` /
     candidate-search / default-fallback won.
   - `src/app/test_runner_new/test_runner_main.spl` prints
     `Running N test file(s) [...] under <binary> (via <source>)` (sequential
     path) and `  binary: <binary> (via <source>)` (parallel path) before
     spawning any child.
   - `check-plan-acceptance-swept.shs` already printed `executed under
     $RUNNER_PATH` in its verdict; it now also prints `plan_acceptance_runner=
     <path> (source: <name>)`.
3. A resolved binary that cannot run specs now fails with a named error
   instead of letting every spec report as an offender:
   - New `simple_binary_supports_run(binary, tmp_dir)` in
     `test_executor_parsing.spl` (mirrors `runner_supports_run` in the shell
     gate: writes a trivial probe `.spl`, runs `<binary> run <probe>`, checks
     exit 0 and the probe's own stdout marker).
   - `test_runner_main.spl` calls it once, up front, in both the sequential
     and parallel dispatch paths, and returns a `TestRunResult` naming the
     unusable binary and its source instead of dispatching any spec.
   - `check-plan-acceptance-swept.shs`'s `resolve_runner()` already had this
     check (`runner_supports_run`); its ERROR message now names which
     variable supplied the rejected binary.

## Additional names found in this family (grep census, 2026-09-06)

Reported, not touched -- a different mechanism, already safeguarded a
different way (see below), out of scope for this fix:

- `SIMPLE_TEST_BINARY`, `SIMPLE_BIN`, `SIMPLE_SEED_BINARY`,
  `SIMPLE_SPEC_COMPILER` -- named in
  `test/03_system/check/test_daemon_env_override_passthrough_spec.spl` and the
  override list in `src/app/test_runner_new/test_runner_client.spl:545-549`
  (plus narrower-scope siblings `CPU_SIMD_RENDER_SCALE_TEST_SIMPLE_BIN`,
  `SIMPLEOS_QEMU_SIMPLE_BIN`). These are per-spec `contract_binary()`
  overrides for ~39 specs that each pick their own exercised binary. The
  failure mode there is different (a stale test-daemon environment silently
  ignoring a caller's override) and was already fixed by forcing the direct
  (non-daemon) execution lane whenever any of these is set -- see that spec's
  docstring. Not folded into `find_simple_binary()`'s precedence chain because
  it is a distinct contract (arbitrary per-spec override, not "the binary the
  runner spawns children with").
- No other 4th name was found for the specific "which binary spawns/executes
  specs" role covered by `find_simple_binary` / `simple_binary` /
  `PLAN_ACCEPTANCE_RUNNER`.

## Verification

```
SIMPLE_BINARY=<binary>          sh scripts/check/check-plan-acceptance-swept.shs --spec-dir <tiny-fixture-dir>
SIMPLE_RUNTIME=<binary>         sh scripts/check/check-plan-acceptance-swept.shs --spec-dir <tiny-fixture-dir>
PLAN_ACCEPTANCE_RUNNER=<binary> sh scripts/check/check-plan-acceptance-swept.shs --spec-dir <tiny-fixture-dir>
```

All three print `plan_acceptance_runner=<binary> (source: <VARNAME>)` and
`PASS`. A binary that rejects `run` (e.g. a shell stub printing `unknown
command 'run'` and exiting 1) produces `ERROR — nothing was checked
('<path>' (from SIMPLE_BINARY) is not usable: not executable, or exists but
rejects the 'run' command)`, exit 2. `--selftest` (12 fixtures) still passes.
