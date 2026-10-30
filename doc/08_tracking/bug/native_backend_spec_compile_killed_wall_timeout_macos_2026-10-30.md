# test_runner_native_backend_spec: native compile killed as wall-timeout on macOS (2026-10-30)

Status: OPEN. The spec stays RED; root cause not yet found.

## Symptom

`test/02_integration/app/test_runner_native_backend_spec.spl` fails 0/2 on macOS
(Darwin 25.5, arm64) for both LLVM and Cranelift.

The first observation was `Native backend producer changed while compiling`.
That was environmental: the shared seed
`src/compiler_rust/target/release/simple` was rebuilt by another session
during the run, at 10:59. `run_test_file_native` correctly refuses a producer
whose sha256 changed mid-compile.

With a private, immutable seed copy, `run_test_file_native` returns this for a
one-example fixture with `--native-backend=cranelift --no-cache --sequential`:

```
Native backend compilation failed: cranelift (exit=-1, limit=timeout,
budget=failure, completion=unavailable); stdout: ; stderr: <seed banner + lint warnings only>
```

The result is the same with `--timeout=1500`. The whole probe, including about
40 s of interpreter load, finished in about 125 s.

## What is known

- The compile child runs as `ExecutionResourceClass.Large` (wall 1,800,000 ms,
  CPU 7,200,000 ms) with `max_wall_ms = options.timeout * 1000`
  (`test_runner_execute.spl:1062`).
- `limit=timeout` means `run_scoped_child` saw
  `TerminationCause.WallTimeout` (`native_owned_process.spl`). A wall timeout
  after about 1 minute does not match either configured deadline.
- `completion=unavailable`: macOS has no process-completion receipt. RLIMIT_AS
  is also unenforced here, according to the `[resource-scope]` notice.

## Next step

Instrument the macOS owned-scope deadline path (`resource_scope.spl`, owned
execution scope). Find which deadline produces `WallTimeout` well before
`max_wall_ms`. Also check whether a native-build of the std.spec closure
finishes at all on this host within the Large budget. Then close the record,
or narrow it to a toolchain or host prerequisite.

The spec is not marked pending: under the seed, a runtime `pending()` inside an
`it` body counts as passed.
