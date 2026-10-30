# Test runner client counts separate option values as spec paths

- **Found:** 2026-10-28
- **Status:** Fixed in this change
- **Severity:** Medium — valid client invocations failed before running the requested spec
- **Component:** `src/app/test_runner_new/client_arg_shape.spl`

## Symptom

The test runner client uses `client_flag_consumes_value` to find positional
spec paths. The helper did not include several options already accepted by the
shared test argument validator, including `--worker-memory-mb`. It therefore
treated that option's value as another spec path and rejected the invocation:

```text
simple src/app/test_runner_new/test_runner_client.spl \
  test/fixtures/phase7_coverage_probe_spec.spl \
  --no-session-daemon --worker-memory-mb 128 --assert-ran
ERROR: expected .spl test file: 128
```

This exact invocation exercises the standalone client entrypoint. The ordinary
`simple test` dispatch has a separate argument path, so the integration guard
invokes the client entrypoint directly for these cases.

## Root cause and fix

The client scanner's value-taking flag list had drifted from
`test_args_validation_error`. It omitted five accepted options that take a
separate value: `--worker-memory-mb`, `--batch-size`, `--session-reset`,
`--sdoctest-env`, and `--profile`; it also omitted `--native-source` and
`--library-mode`. The scanner now includes the complete 28-flag public
`needs_value` set. Inline `--name=value` forms and boolean aliases remain
non-consuming; adapter-only and equals-only private options are not added to
the public list.

## Evidence

Using the pinned `aa58` bootstrap seed in interpreter mode:

- Before the fix, the command above exited 1 with `expected .spl test file: 128`.
- After the fix, it exited 0 with `--assert-ran`.
- `test/03_system/app/test_runner/feature/client_arg_shape_spec.spl`: 4 examples passed.
- `scripts/check/check-test-runner-single-lane-paths.shs`: 8 invocations passed, including path-shaped values, a permitted negative decimal, and rejection of `--` as a missing timeout value.

The pinned executable prints a warning that it is a Rust-built bootstrap seed
and should not be used as the normal tool. These results are diagnostic seed
evidence; they do not claim a run with the pure-Simple release binary.
