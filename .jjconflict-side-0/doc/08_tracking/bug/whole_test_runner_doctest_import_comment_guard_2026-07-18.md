# Whole test runner skipped comment-only mode

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
