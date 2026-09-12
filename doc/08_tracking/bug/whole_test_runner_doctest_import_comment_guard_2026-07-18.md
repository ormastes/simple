# Whole test runner skipped comment-only mode

**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

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

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule C: filed before 2026-07-29, no runnable repro in the record, no status line existed); closed as stale per the "too old / not valid -> close" triage policy. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification if reopened.
