# Stage2 positional hello-world native build rejects its backend session token

Status: OPEN. The former silent exit now emits a diagnostic, but the session
token rejection still blocks Stage2 admission and therefore Target 5/6 native
size, startup, compile-time, and RSS qualification. It is separate from the
fixed `dynlib_lifetime_owner_v1.spl` HIR type error.

## Evidence

The current-source Cranelift Stage2 native build compiled 595 files, reused
426, failed zero, and linked a 47,135 KB candidate in 377.4 seconds. The
admission gate preserved that candidate at
`build/bootstrap-target56/stage2/aarch64-unknown-linux-gnu/simple.rejected`.
Its `SIMPLE_BOOTSTRAP=0` positional hello-world smoke exited 1 without an
error line. The retained smoke log is
`build/bootstrap-target56/stage3/aarch64-unknown-linux-gnu/stage2-sanity.env.frontend-bootstrap-0.log.hello-world-positional`.

The same candidate reproduces in under one second with the isolated fixture
`scripts/check/cert/redeploy_gate/fixtures/hello_world.spl`, Cranelift,
`core-c-bootstrap`, `--entry-closure`, `--mode one-binary`, positional entry,
`SIMPLE_PACKAGE_INDEX_COLD_INIT=1`, and `SIMPLE_BOOTSTRAP=0`. Local logs are
under `build/mini_builds/target56_dynlib_probe/`: `positional_repro.log`,
`positional_trace.log`, and `native_trace.log`. The source passes parsing,
HIR, MIR, borrow check, async processing, MIR optimization, AOP weaving, and
debug trace. `SIMPLE_COMPILER_PHASE_PROFILE=1` shows the last marker
`aot:format:done`, followed by exit 1. `SIMPLE_COMPILER_TRACE=1` emits no
`[NATIVE]` marker from `_compile_to_native_with_backend_session`.

`bootstrap_main.spl` selects `OutputFormat.Native`; `aot_compile()` routes
that format to `compile_to_native()`. For Cranelift,
`driver_aot_uses_versioned_backend()` returns true, and
`BackendSessionOwnedLeaseV2.open()` runs before the first `[NATIVE]` marker.
The trace therefore narrows the failure to that dispatch/session boundary or
an unresolved call into it; it does not yet prove which expression fails.
The frontend smoke only reports raw exit 1 and the compiler's
`compile_result_errors()` loop prints no message.

## Session-open diagnosis

Opt-in markers added around native output dispatch show that the candidate
passes plugin selection and request construction, then
`BackendSessionOwnedLeaseV2.open()` returns `Err`. The previous implicit
`error.to_text()` rendering also failed silently before the error could be
printed. An explicit match over `BackendSessionAuthorityErrorV2` variants now
reports `BACKEND_SESSION_AUTHORITY: unknown or substituted session` in the
Stage2 sanity log. The last build compiled 3 files, reused 1,018, and failed
zero before reaching the same admission refusal.

`backend_session_authority_open_v2()` can return only `InvalidOwner`,
`CapacityExceeded`, `CounterOverflow`, or `LoadRejected`. The wrapper then
calls `backend_session_authority_project_v2()`, which can return
`UnknownOrSubstituted`. The observed error therefore points to token
projection after opening. It has not yet been proven whether the owner lost
its newly appended record, token equality fails under native codegen, or a
different authority invariant is violated.

## TODO

Add a focused native probe inside the authority owner that records the new
record count and each token field before projection, without relying on
struct equality. Compare those values with the caller's token, then repair
the failing invariant. Re-run the positional fixture before full Stage2
admission. Keep the three-cycle verify/fix cap for the next scoped session;
do not cite the linked candidate as admitted.
