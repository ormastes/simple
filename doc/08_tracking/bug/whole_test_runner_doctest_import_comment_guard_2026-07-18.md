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

## Discovery and registration follow-up

Repository inspection found that source documentation predominantly uses
ordinary `#` fences and fenced triple-quoted docstrings, while the source
extractor previously recognized only `///`, `##`, and explicit docstring
`sdoctest:` sections. The manifest scanner also maintained a separate exact
` ```simple ` / ` ```spl ` counter, so modifier fences, malformed-fence rules,
and all source-comment examples could disagree with execution.

The canonical ownership is now:

- `sdoctest.extractor` parses Markdown blocks and modifiers.
- `doctest_runner.extract_doctests` parses source comments and docstrings.
- `test_manifest_scanner` calls those extractors instead of duplicating their
  grammar.
- Markdown and source doctest execution rescans configured or explicit inputs
  at the run event. The test manifest remains a five-minute TTL cache with
  size/mtime incremental reuse; `--refresh-manifest` handles bulk moves.
- `simple check`/`lint` validates Simple source semantics. It does not own a
  second doctest registry or fence grammar.

The static inventory after widening source discovery is approximately 1,059
source candidates (281 comment fences, 680 fenced docstrings, 98 docstring
`sdoctest:` sections), compared with roughly 100 recognized by the old forms.
Markdown contains approximately 136,187 executable-fence candidates before
configured ignore rules and closed/non-empty extraction are applied.

Focused `simple check` passed for `doctest_runner.spl` and
`test_manifest_scanner.spl`. The focused executable spec reached the runner but
was blocked first by the known test-daemon timeout and then by the deployed
runtime's missing `rt_process_run_bounded` extern; these are environment gates,
not passing runtime evidence.
