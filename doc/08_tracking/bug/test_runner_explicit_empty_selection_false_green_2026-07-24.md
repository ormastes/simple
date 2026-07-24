# Test runner explicit empty selection false-green

## Status

Source fix implemented; fresh pure-Simple qualification is blocked by the
eager/module-loading crash described below.

## Reproduction

An explicit missing `*_spec.spl`, an existing non-test `.spl`, or an empty
directory discovers zero spec files. The runner previously returned a
zero-valued `TestRunResult`, and `TestRunResult.is_ok()` converted that result
to exit status 0.

## Root cause and fix

`parse_test_args` replaced an absent path with `test/`, losing whether the user
had supplied a path. `TestOptions.path_explicit` now preserves that provenance.
The production runner reuses `classify_test_run_result`: an explicit empty spec
selection maps to `EmptySelection` (exit 4), while an implicit default sweep,
`--list`, and the explicitly selected SPL-doctest lane retain zero-selection
success. Empty selections are not written to the test database.

The same provenance bit replaces `path != "test/"` guesses in both doctest
owners, so an explicitly named `test/` remains explicit.

## Regression coverage

`test/01_unit/lib/test_runner/args_parsing_spec.spl` checks implicit versus
explicit paths and the empty-selection policy. The intended CLI controls are:

- explicit missing/non-test/empty spec targets: exit 4;
- a valid explicit spec: exit 0 when its assertions pass;
- an implicit empty default sweep and explicit `--list`: exit 0;
- `--spl-doctest file.spl`: owned by the doctest lane, not rejected by the
  empty spec lane.

## Qualification blocker

Focused incremental validation used
`release/x86_64-unknown-linux-gnu/simple`; no bootstrap or full build was run.
The retained pure-Simple executable:

- passed `check src/lib/nogc_sync_mut/test_runner/test_runner_args.spl`;
- passed `check src/app/test_runner_new/test_runner_main.spl`;
- then terminated with SIGSEGV while checking other touched consumers and
  while fresh-running the CLI source.

The three-attempt cap was reached, so validation stopped instead of retrying.
This is consistent with the active eager/module-loading instability: changing a
widely imported struct can crash a consumer before runner code executes.
Consequently this patch must not be marked verify-PASS until a fresh
pure-Simple incremental artifact runs the focused CLI controls above.

## Related

- `doc/08_tracking/bug/rust_test_runner_explicit_non_test_false_green_2026-07-17.md`
- `doc/08_tracking/bug/test_runner_zero_executed_single_file_greenwash_2026-07-17.md`
- `doc/08_tracking/bug/test_runner_fresh_seed_silent_noop_2026-07-17.md`
