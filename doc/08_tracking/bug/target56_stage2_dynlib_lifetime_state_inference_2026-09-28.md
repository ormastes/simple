# Target 5/6 current-source Stage2 cannot infer dynlib lifetime state

Status: OPEN. This blocks an admitted Stage4 compiler for the Target 5/6
size, startup, and persistent-index qualification lanes.

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

## Next action

On a fresh scoped session, use the fast bootstrap-mode reproduction to isolate
the first rejected `entries` expression with the same seed and current source,
preserving the phase cache. Add a focused
regression that proves the real `Mutex` state remains
`_DynlibLifetimeStateV1` through each lock callback, then repair the
compiler or owner without changing close/borrow behavior. Run the existing
cached-slot/aliased-handle scenario and resume Stage2 admission only after
the focused case passes. Keep the three-cycle cap for that new session.
