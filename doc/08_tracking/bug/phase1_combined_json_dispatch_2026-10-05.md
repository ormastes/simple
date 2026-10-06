# Phase 1 combined JSON dispatch

Status: wrapper corrected; focused orchestration tests PASS; real whole-run
verification remains pending. This does not close existing test failures.

The `phase1-seed283f-whole-walkfix20-1` attempt exited 1 after 3219.73 seconds.
Its callback reported `INFRASTRUCTURE_FAILED: expected one combined runner
summary`. The source was `C:/snp/phase1-whole-walkfix`.

The callback used `--format=json`. Direct seed dispatch in
`src/app/test_runner_new/test_runner_main.spl` recognizes `--json` and the two
arguments `--format json` for combined output. The equals form reached the
spec formatter, yielding only a spec JSON object rather than a combined result.

Use the supported `--json` argument in the bootstrap callback. Two focused
boundary tests exercise the complete callback and receipt classifier with a
mode-sensitive fake subprocess: complete category output is preserved, and
doctest failures remain failures. These are orchestration tests, not evidence
that real Simple tests passed.

Retained real stdout reports 315 SPL doctest passes and 168 failures, and 1652
Markdown passes, 1 failure, and 87 errors. The spec phase reports 2134 coverage
metadata errors with no executed spec assertions. These are partial human
summaries; do not manufacture a combined qualified result from them.

The three-attempt whole-run limit was reached. Preserve the failed receipt;
verify the corrected callback at the next separately scoped bootstrap run.
