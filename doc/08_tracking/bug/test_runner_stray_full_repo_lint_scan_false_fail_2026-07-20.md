# bin/simple test: stray full-repo lint scan inflates duration and flips a fully-green spec to FAIL

**Status:** Open
**Category:** GENUINE-BUG (test-runner / interpreter side effect)
**Discovered:** 2026-07-20 (whole-suite triage campaign, shard meas_01u_03)

## Symptom

Running the single spec below reports `FAIL` / `Failed: 1` even though every
`it` example inside the spec passes (`Passed: 16`, zero `✗` lines, all three
`describe` blocks individually print `N examples, 0 failures`):

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 \
  /home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple \
  test test/01_unit/app/llm_caret/provider_spec.spl --no-session-daemon
```

Output tail:
```
  ✓ creates error response

1 example, 0 failures
Usage: simple_lint <file.spl> [options]
...
warning: Deprecated syntax for type parameters
  --> /home/ormastes/dev/pub/simple/src/lib/common/string_core.spl:89:44
...
[hundreds of thousands of lines: lint warnings for essentially every .spl
file under src/compiler/**, src/lib/**, src/app/**]
...
error: test-runner: spec failed

=========================================
Test Summary
=========================================
Files: 1
Passed: 16
Failed: 1
Duration: 15380ms

FAIL test/01_unit/app/llm_caret/provider_spec.spl
```

Immediately after the last real test example finishes, the process prints the
`simple_lint` CLI usage banner (`Usage: simple_lint <file.spl> [options]`) as
if invoked with no/bad arguments, then proceeds to **lint-scan the entire
repository source tree** (`src/compiler/**`, `src/lib/**`, `src/app/**`,
hundreds of thousands of warning/info lines: "Deprecated syntax for type
parameters", "Avoid 'export use *'", "Common mistake detected: ... self is
implicit in methods", etc.) before finally reporting `error: test-runner: spec
failed` and `Failed: 1` — with no corresponding `✗` anywhere in the actual
spec output.

Effects:
- A fully green spec (16/16 assertions pass) is reported as `FAIL`.
- Wall-clock duration balloons (observed 14–15s consistently, and the run
  intermittently exceeds even a 90s timeout under load), because the process
  is scanning/linting the whole source tree, not just the one spec file.
- The extra `Failed: 1` count has no traceable assertion — it does not
  correspond to any `it` block.

## Minimal repro

`test/01_unit/app/llm_caret/provider_spec.spl` is already minimal (94 lines,
3 `describe` blocks, 16 `it` examples, only imports
`app.llm_caret.provider.{list_providers, is_valid_provider, new_llm_error}`).
No changes to the spec are needed to reproduce; every example passes when
inspected individually.

## Root-cause hypothesis

Not confirmed (out of scope for this pass — src/** changes are not permitted
under this shard's task rules). Candidates to investigate:
1. Something in the `app.llm_caret.provider` import chain (or a module it
   transitively pulls in) calls into `src/compiler/90.tools/lint/main.spl`
   (the `simple_lint` entry point) with no arguments, e.g. via a doctest /
   coverage hook that defaults to "no file given → scan whole repo" instead
   of failing fast or being skipped in test context.
2. `bin/simple test`'s test-runner may run an implicit lint/doctest sweep as
   a post-pass step for specs under certain paths (e.g. `app/llm_caret/**`)
   and mis-attributes the lint tool's non-zero exit (from warnings, not
   errors) as a spec failure (`Failed: 1`) even though no assertion failed.
3. `simple_lint`'s CLI arg parsing may fall through to a "scan cwd
   recursively" default when it prints "Usage: ..." on bad/missing args
   instead of exiting immediately — worth checking
   `src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl` and
   `src/compiler/90.tools/lint/main.spl` for a missing early-return after the
   usage print.

## Why not classified STALE-TEST

Per campaign guide rules, weakening/dropping assertions to force green is
forbidden, and this spec has no assertion to weaken — all 16 `it` blocks
already pass. The failure is entirely a test-runner/side-effect artifact
external to the spec's own logic, so this is filed as GENUINE-BUG rather than
edited away.

## Affected specs (this shard)

- `test/01_unit/app/llm_caret/provider_spec.spl` (confirmed, reproduced twice)
