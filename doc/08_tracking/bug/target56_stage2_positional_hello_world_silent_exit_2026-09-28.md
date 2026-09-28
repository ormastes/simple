# Stage2 positional hello-world native build reaches AOT with an empty diagnostic

Status: OPEN. The session-token rejection is fixed in the focused native
candidate, but Cranelift V2 module construction still returns zero and AOT
cannot publish a readable backend reason.
Stage2 admission and Target 5/6 native size, startup, compile-time, and RSS
qualification remain blocked. This is separate from the fixed
`dynlib_lifetime_owner_v1.spl` HIR type error.

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

## Fieldwise token repair and next AOT failure

The next native candidate traced one authority record with owner ID 1,
generation 1, and the same receipt hash as the returned token. Direct
whole-struct token equality in `_backend_session_record_index_v2()` therefore
rejected matching fields. The authority, compile-use, and result-token index
helpers now compare their token fields explicitly. The following Stage2 build
compiled 3 files, reused 1,018, and failed zero; its positional smoke passed
session projection and reached Cranelift direct AOT. This proves the original
`UnknownOrSubstituted` boundary was removed in that native fixture.

The new failure is `backend object-path status 1`. The AOT diagnostic writer
reports that its atomic write failed; the driver then cannot read the
diagnostic file. A temporary bounded console fallback printed a blank line
where the backend reason should have appeared, so that fallback was reverted.
The writer/adapter path is in
`src/compiler/70.backend/backend_plugin/builtin_adapter.spl` and
`src/compiler/70.backend/backend_plugin/target_context_v2.spl`. Both test
`diagnostic != ""` before rejecting; native code elsewhere documents that a
nil string can satisfy that comparison while `len()` is negative. This is a
plausible cause, not yet proven. The temporary probe was removed from the
authority owner before commit.

## Cranelift constructor boundary

Changing those diagnostic guards to `len() > 0` did not change the native
failure, so that experiment was reverted. The smoke prints
`[cranelift-direct] start` and `target`, but never `module`: the
`cranelift_new_aot_for_request_v2()` call returns zero. Source inspection
found a definite bootstrap request mismatch: `bootstrap_main.spl` set
`options.opt_level = 3` for Cranelift, while the V2 Rust constructor accepts
only exact optimization modes 0, 1, and 2. The bootstrap CLI now explicitly
selects Cranelift's highest admitted mode, 2, leaving other backends at 3.
That policy correction compiled 2 files and reused 1,019, but admission still
failed before module creation.

A debugger breakpoint on `spl_cranelift_new_aot_module_config_v2` in the
rejected candidate confirmed the actual Rust ABI argument `opt=2`.
The first debugger attempt did not decode the target, CPU, or feature text
because GDB does not support `*` width in its `printf` command. Thus the
remaining constructor rejection may be a malformed text argument, a
noncanonical target triple, unsupported ISA, or another V2 check; the current
evidence does not distinguish them.

## TODO

Read the V2 constructor's name, target, CPU, and feature byte ranges at the
retained breakpoint using each explicit length (for example GDB Python
`inferior.read_memory`). Determine which of `strict_abi_text`, canonical
triple parsing, ISA lookup, feature admission, or `builder.finish` returns
zero, then repair that input or provider path without substituting the
requested optimization mode. Re-run the positional fixture and full Stage2
admission. Keep the three-cycle verify/fix cap for the next scoped session;
do not cite the linked candidate as admitted.
