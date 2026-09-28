# Target 5/6 current-source Stage2 cannot infer dynlib lifetime state

Status: DYN-LIFETIME HIR ERROR FIXED; full Stage2 native build passes, but
admission is blocked by a separate hello-world positional smoke failure.
Target 5/6 size, startup, and persistent-index qualification remain pending.

## Reproduction

In the isolated `/home/yoon/dev/simple-target56-completion` worktree at
`45348442c4a7bee1a805b5df8e608d97e6dd9bba`, run the canonical
receipt-free Stage2 lane with `--full-bootstrap --stop-after-stage2`,
`--strategy=normal`, `--backend=cranelift`, `--jobs=2`, and
`--output=build/bootstrap-target56`. LLVM 23 is unavailable on this host,
so the default LLVM route aborts before compilation. The Cranelift preflight
passes 5/5. Its locally built bootstrap seed has SHA-256
`9cb049fd642bfec4c33a35ebb40464070cc26ad775764ac1f86ebaccb97fd8e8`.

The seed compiles 1,018 files and refuses one:
`src/lib/nogc_sync_mut/sffi/dynlib_lifetime_owner_v1.spl`, with
`hir: Cannot infer field type: struct 'i64' field 'entries'`. The complete
log is retained at
`build/bootstrap-target56/logs/aarch64-unknown-linux-gnu/stage2-native-build.log`.
No Stage2 admission or Stage4 CLI was produced.

## Bounded diagnosis

Three Stage2 verify/fix cycles were used in this session:

1. Unmodified current source reached the HIR `i64.entries` error.
2. Explicit `\state: _DynlibLifetimeStateV1:` lambda annotations failed
   parsing at line 47:92 (`expected Comma, found Colon`) in this seed.
3. A typed callback wrapper around `mutex_with_lock` parsed but reached the
   same HIR `i64.entries` error.

Both source experiments were reverted. The error may arise from the seed's
generic closure inference or another field access in this owner; these runs
do not prove which. No semantic workaround or successful bootstrap is claimed.

## Fast bootstrap-mode reproduction (continuation)

The Stage2 command transcript supplied the missing diagnostic mode:
`SIMPLE_BOOTSTRAP=1` and `SIMPLE_NATIVE_BUILD_RUST=1`, with the
`kernel_llvm_cranelift` composition, Cranelift, `core-c-bootstrap`, and
`SIMPLE_NO_STUB_FALLBACK=1`. A 36-file entry closure rooted at
`build/mini_builds/target56_dynlib_probe/main.spl` reproduces the same
`i64.entries` HIR error in about three seconds. Its first run compiled 35
files and failed one; a source-only retry compiled one and reused 34. The
diagnostic entry lies under ignored `build/`, so this probe explicitly uses
`SIMPLE_SCV_FREEZE_FALLBACK=1`. It is not SCV admission or performance proof.
Logs and the isolated cache are retained under
`build/mini_builds/target56_dynlib_probe/` (`build_bootstrap.log`).

Making the five `mutex_with_lock` generic arguments explicitly
`_DynlibLifetimeStateV1` did not change the HIR error
(`build_bootstrap_explicit.log`). `SIMPLE_TRACE_FIELD_GET=1` emitted no
field-failure context for this case (`build_bootstrap_trace.log`). That edit
was reverted. A separate one-file generic-callback native fixture failed
with `E-MONO-032` (uninferred generic call), which is suggestive but does not
prove the owner error has the same cause. Ordinary `simple compile` accepts
the owner as bytecode; ordinary native build instead stops earlier at parser
errors for this source, so neither is a substitute for the bootstrap-mode
reproduction.

## Windows current-main confirmation (2026-09-28)

An independent Windows MSVC full bootstrap at `e465b19cc00a706c487d788e1830cfa9ce91c001` rebuilt the Rust authority with LLVM 23.1.1 and reached the same `hir: Cannot infer field type: struct 'i64' field 'entries'` rejection during Stage 2. It also found an independent `src/math/rendering.spl` unresolved `to_latex` call. The Stage 2 compiler test matrix did not start. The full log is `D:/dev/simple-windows-bootstrap-20260927/build/bootstrap/windows-linux-20260927/windows/logs/x86_64-pc-windows-msvc/stage2-native-build.log`.

A one-file bootstrap-mode probe retained under `build/mini_builds/win_dynlib_probe/` reproduced the owner rejection in under a second. Truncating the probe before `dynlib_lifetime_register_v1` linked successfully; including registration reproduced `i64.entries`. Expanding its compact return, expanding the lookup's compact branches, and updating typed state directly under the mutex did not remove the rejection. All three source experiments were reverted. This narrows the first failing function but does not identify the specific field expression or establish a safe fix.

## Isolated diagnosis and source repair

A diagnostic seed instrumented at field access showed that
`_dynlib_lifetime_index_v1` receives the declared
`_DynlibLifetimeStateV1`, but the first `state.entries` in
`dynlib_lifetime_register_v1` sees the `\state` update-closure parameter as
`i64`. The same source also contains four more update closures. The temporary
Rust instrumentation was reverted. The lifetime owner now updates its typed
Simple-side state directly while holding the existing mutex in each operation;
`dlclose` remains after unlock in the end and retire paths. This removes the
closure inference failure without changing the admission/retirement sequence.

The 36-file bootstrap-mode native repro compiled with zero failures and linked
a 74 KB probe (`build/mini_builds/target56_dynlib_probe/direct_lock.log`). The
current-source interpreter spec executed 14 cases: both cached-slot/aliased-
handle and borrowed-mapping lifetime cases passed. Its final unrelated
pre-publication refusal case failed because the fixture's
`spl_plugin_entry_v1` symbol was unresolved, so the full spec is not green.
The first full Stage2 rerun stopped in its RSS watchdog: process observation
exceeded the default 1,000 ms budget, despite a 1.33 GiB observed peak below
the unchanged 5.59 GiB cap. A second run set the watchdog's supported
`SIMPLE_PROCESS_TREE_OBSERVATION_BUDGET_MS=5000`. It compiled 595 files,
reused 426, failed zero, and linked the 47,135 KB Stage2 binary in 377.4 s.
The subsequent frontend admission smoke failed: the Stage2 compiler's
positional hello-world native build exited 1 after AOP weaving with no
diagnostic. The candidate remains at
`build/bootstrap-target56/stage2/aarch64-unknown-linux-gnu/simple.rejected`;
see `build/bootstrap-target56/stage3/aarch64-unknown-linux-gnu/stage2-sanity.env.frontend-bootstrap-0.log.hello-world-positional`.
No Stage2 admission, Stage4 CLI, or Target 5/6 performance proof exists.

## Next action

Reproduce the rejected Stage2 binary's silent positional hello-world failure
as a focused case, identify its first failing phase after AOP weaving, and
repair that path. Then rerun Stage2 admission and resume Stage3/4 from admitted
artifacts. Run the Target 5/6 size, startup, compile-time, and RSS cohorts
before marking either target complete.
