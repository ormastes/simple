# validate_system_test_covers skips Windows backslash paths

`validate_system_test_covers` (src/lib/nogc_sync_mut/test_runner/test_runner_files.spl, and the
app copy src/app/test_runner_new/test_runner_files.spl) matched the literal `/system/`, so a
Windows path such as `test\system\x_spec.spl` skipped the `# @cover` admission check and
`scripts/check/check-test-runner-cover-admission.shs` exited 1 on Windows.

Fix: normalize `\` to `/` before matching (both copies). Spec:
test/01_unit/app/test_runner_new/system_cover_backslash_spec.spl (2 of 5 cases failed before).

Sibling `"/xxx/"` literal matches with the same pattern, NOT fixed here (paths there are
produced by discovery, which already normalizes base_path, but direct callers with backslash
paths would misclassify): app/test_runner_new/execution_strategy.spl:102-116,
test_runner_files.spl:118-122,300,403-416, test_runner_main.spl:907, test_runner_single.spl:1398;
lib test_classification.spl:40,137-139, test_manifest_scanner.spl:220-224,
test_runner_execute.spl (resource_class "/03_system/"), test_runner_metrics.spl:27-29,
test_runner_single.spl:182.

Also observed: the seed lexer rejects `"test\unit\x"` ("Invalid unicode escape: \u requires
hex digits") -- `\` followed by `u` is mis-lexed; spec builds backslashes via join instead.
