# Self-hosted codegen worker crash on sosix.stdio with runtime-owner (native_all) config

Date: 2026-11-05
Host: Windows 11, 31.7 GiB RAM, llvm-mingw 20260922, cranelift backend
Lane: work/simple-hardening-release-20261013 (wave-1 stronger-types verification)
Compiler under test: admitted stage-2 trust root (candidate 742c3d31eb99...,
itself built from wave-1 sources f957a28)

## Observation

Standalone self-hosted `native-build` of the test-runner entry
(`src/app/test_runner_new/main.spl`, 322-module closure) succeeds end-to-end
with `--runtime-bundle core-c-bootstrap` (compile + 40-min codegen monolith +
link attempt). With the default bundle plus `--runtime-path
<stage2-runtime-authority>` (the configuration that admits
libsimple_native_all.a and the full hosted system-library list), the build
deterministically dies ~35-40 ms after `native_compile` starts its serial
lane, at the same module position (`lib.nogc_async_mut.sosix.stdio`):

```
[build] phase=native_compile ... done=61 total=322 ... current=lib.nogc_async_mut.sosix.stdio
!!!!!! END NATIVE-BUILD TRUNCATED STDERR !!!!!!
  interpreter: .../stage2/.../simple.exe (exit code 1)
```

No diagnostics survive (worker stderr is truncated with no preserved error
lines; the spill log ends at the same line). Reproduced three times with
identical timing, including with a fresh output key (ruling out a poisoned
cache entry). The same module compiles successfully under
core-c-bootstrap, so the crash is config-dependent
(native_all/runtime-owner inputs to codegen), not module-inherent.

## Related: manual-link runtime misbehavior

Linking the produced objects by hand (261 module .o + 45 runtime .o +
libsimple_runtime.a + libsimple_native_all.a + full windows lib set, with
--allow-multiple-definition) produces a runnable test-runner binary, but the
binary cannot see process argv: `get_cli_args()` returns [] (verified via a
banner whose state tracks parsed options; env vars ARE observed). Root
cause partially isolated: `sys_get_args` exists as a WEAK definition in
`runtime_native.o` (correct, argv-registering) and a STRONG stale definition
in `libsimple_runtime.a` (Rust-archive member
simple_runtime...-cgu.09.rcgu.o); the strong one wins under any link order.
Renaming the stale symbol and relinking with the generated entry object
still yields empty argv, so a second preemption/ordering problem remains
(the --allow-multiple-definition duplicate std:: symbols between the two
archives are the likely next suspect). A faithful owner-archive link
(`llvm_runtime_owner_c_gnu_archive_v1`) is the sanctioned path and cannot
be reached because the build dies before linking.

## Impact

- Stage-2 trust-root admission itself is unaffected (receipts issued; full
  sanity matrix passed).
- Downstream tool builds (full CLI, standalone test runner) cannot complete
  through the sanctioned path on this host; spec execution for the wave-1
  stronger-types changes is blocked behind this crash (or behind the
  separate host commit-limit wall for the 3004-module full CLI,
  doc/08_tracking/bug/mir_shard_commit_blowup_full_closure_2026-11-05.md).

## Suggested direction

1. Reproduce with the codegen worker's stderr preserved
   (`SIMPLE_MIR_SHARD_ONLY_PATHS`-style restriction to
   lib.nogc_async_mut.sosix.stdio, debug build of the stage-2 compiler) to
   capture the actual crash (suspected access violation in the codegen of
   the stdio module when runtime-owner symbols are in scope).
2. Audit `sys_get_args` ownership: the weak/strong duplication across
   runtime_native.o and libsimple_runtime.a looks like a stale archive
   member that should not export the symbol.
3. Consider admitting the os/sosix closure into the stage-2 sanity matrix
   so config-dependent codegen crashes surface during admission.

## Status

OPEN. Blocks wave-1 spec execution; tracked from PR #7017
(work/simple-hardening-release-20261013).
