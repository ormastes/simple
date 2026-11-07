# Field indices on by-value and erased receivers

**Status:** AUTHORED / NOT_RUN. This manual mirrors the single executable scenario in [the spec](../../../../../test/01_unit/compiler/hir/field_index_erased_receiver_spec.spl). Native execution and docgen validation are pending an admitted full CLI.

The regression fixture uses a `Triple` with distinct nonzero field values 11, 13 and 17. If field resolution silently substitutes index 0, the wrong output is recognizable as 111111. The scenario invokes a real compiler and its generated executable; source inspection or a mocked child cannot satisfy it.

## Prepare the real compiler fixture

1. Supply an absolute admitted full CLI through `SIMPLE_BIN` and execute from an absolute isolated workspace. The helper refuses missing/relative runtime or workspace paths.
2. Create `build/test-artifacts/field_index_erased`, remove the previous output binary, and check both setup exit codes. Each setup child has a 5-second deadline and 64 KiB capture bound.
3. Write the exact fixture source and require successful canonical `file_write`. Failure returns before compiler launch, preventing stale source from being accepted.
4. Launch direct argv through `/usr/bin/env`, setting `SIMPLE_BOOTSTRAP=1` only for the child. Compile the source closure with `--threads 1`; the native-build parser supports that option.
5. Bound compilation to 120 seconds and 4 MiB output capture. Retain `build.stdout.log` and `build.stderr.log`, assert the real exit status, and return failure before product execution on a nonzero status.
6. Run the fresh absolute output with a 10-second deadline and 64 KiB capture bound. Retain `run.stdout.log` and `run.stderr.log`; require exit zero.

Log writes are attempted by the current helper but their success is not asserted. The coordinator must retain independent outer stdout/stderr and watchdog receipts; absent log files cannot be presented as evidence that logging succeeded.

## Check all three receiver shapes

1. Reject any `BUILD-FAILED` marker and require the direct-output marker.
2. Remove newlines for engines whose `print` output differs only in newline behavior.
3. Require `DIRECT111317` for fields read from a local binding of the returned struct.
4. Require `CALL111317` for fields read directly from call expressions, exercising the erased-receiver route.
5. Require `FWD111317` for a value forwarded through another returning function.
6. Reject 111111 anywhere in the output, catching the field-zero substitution fingerprint.

These are three related receiver shapes inside one executable scenario, not three independently discovered tests. The fixture reproduces the historical wrong-field mechanism; runtime execution is still required to establish behavior for the current compiler/provider.

## Ownership, evidence and limits

The campaign coordinator binds `SIMPLE_BIN`, `SIMPLE_BINARY` and `SIMPLE_OWNERSHIP_TEST_RUNTIME` to the same immutable admitted full CLI and records source/runtime/provider identities. The fixed fixture path requires an isolated workspace and serialized execution.

Use the canonical outer process-tree watchdog with the manifest’s 180-second cap. An inner bounded-process timeout is not proof that all descendants were reaped. Preserve unresolved cleanup ownership and do not start replacement work until the coordinator establishes retirement. No shell fallback, Rust seed execution, or automatic deadline increase is admitted by this manual.

Acceptance requires one actually discovered/executed scenario, all assertions passing, real compiler/product exit records and the outer lifecycle receipt. A timeout, missing compiler, failed source write or absent output is a failure, never a skip or PASS.

After runtime admission, run real `spipe-docgen` for this exact spec with `--output doc/06_spec --no-index`; require complete documentation and `0 stubs`. Execution and docgen are **NOT_RUN**. This manual does not qualify all compiler field-resolution paths or descendant containment.
