# test_runner_native_backend_spec: native compile hits the 120 s test deadline on macOS (2026-10-30)

Status: OPEN. The spec stays RED.

## Symptom

`test/02_integration/app/test_runner_native_backend_spec.spl` fails 0/2 on macOS
(Darwin 25.5, arm64) for both LLVM and Cranelift.

The first observation was `Native backend producer changed while compiling`.
That was environmental: the shared seed was rebuilt by another session during
the run. `run_test_file_native` correctly refuses a producer whose digest
changed (`test_runner_execute.spl:1222`).

With an immutable private seed copy, a one-example fixture returns:

```
Native backend compilation failed: cranelift (exit=-1, limit=timeout,
budget=failure, completion=unavailable)
```

## Cause (from code reading; the confirming run is still to do)

- The compile child's only wall deadline is `options.timeout * 1000`
  (`test_runner_execute.spl:1062`). `native_owned_process.spl:25` puts it into
  `ResourceBudget.max_wall_ms` and ignores the Large class default.
  `options.timeout` defaults to 120 s.
- On macOS, the owned observed runner is `ENOTSUP`. The scope falls back to
  `process_run_bounded` (`resource_scope.spl` legacy fallback), which SIGKILLs
  the group at the deadline and reports `WallTimeout`. That explains
  `limit=timeout`, `budget=failure` and `completion=unavailable`.
- Most likely, a whole native build of the `std.spec` +
  `app.test_runner_new.test_runner_args` closure takes longer than 120 s on
  this host.

The probe passed `--timeout=1500`, but that form is not recognised: only
`--timeout N` is (`test_runner_args.spl:373-376`). The flag was silently
ignored, so the probe did not test a longer deadline.

## Next step

1. Rerun the probe with `--timeout 1500`.
2. Measure the native compile duration of the fixture closure.
3. Then either raise the spec's compile deadline, speed up the build, or
   record the host as too slow.

Also consider accepting `--timeout=N`, or rejecting it loudly, instead of
dropping it silently.

The spec is not marked pending: under the seed, a runtime `pending()` inside
an `it` body counts as passed.
