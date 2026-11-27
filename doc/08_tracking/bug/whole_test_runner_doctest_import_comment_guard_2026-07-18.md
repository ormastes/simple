# Whole test runner skipped comment-only mode
## Closed 2026-09-16 — ...un as having no enabled test lane. ## Fix and prevention The app entrypoint now imports th

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

## Symptom

The deployed app runner imported `run_spl_doctest_mode` from a module that does
not define it. Its early configuration guard also treated a comment-doctest-only
run as having no enabled test lane.

## Fix and prevention

The app entrypoint now imports the function from `test_runner_modes` and the
guard considers spec, Markdown, and comment doctest lanes. The whole-release
source regression reads the deployed app entrypoint and pins the import, guard,
and both doctest dispatches.

Static source checks pass. Runtime and whole-suite proof remain pending under
this session's execution restriction.


## Runtime verification 2026-11-25 — pending proof now collected

Verified on Windows worktree `D:\wt-p3-bae` (branch `work/p3-bae-20261125`,
base `origin/release/1.0.0`) with the tracked `bin/simple.exe`,
`SIMPLE_LIB=src`:

- Source fix still present: `src/app/test_runner_new/test_runner_main.spl:66`
  imports `run_spl_doctest_mode` from `std.test_runner.test_runner_modes`
  (defined at `src/app/test_runner_new/test_runner_modes.spl:42`), and the
  lane-selection guard at `test_runner_main.spl:1497-1546` considers the spec,
  Markdown (`--sdoctest`), and comment-doctest (`--spl-doctest`) lanes.
- Runtime proof (the part previously pending): a comment-doctest-only run,

  ```
  bin/simple.exe test probe_doctest2.spl --spl-doctest
  ```

  where the probe file contains only an `sdoctest:` docstring block and no
  spec, is dispatched to the SPL-doctest lane instead of being skipped as
  having no enabled test lane: output `SPL Doctest: Running doctests from 1
  source file(s)... PASS ... (1 passed, 0 failed)`, summary
  `1 passed, 0 failed, 0 skipped`, exit 0.

The "Runtime and whole-suite proof remain pending" caveat is now discharged
for the runtime half; the closure stands.
