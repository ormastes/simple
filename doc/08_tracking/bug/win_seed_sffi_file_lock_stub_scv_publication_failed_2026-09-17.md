# Windows seed-runtime SFFI `rt_file_lock` stub blocked SCV inventory publication

Date: 2026-09-17
Lane: kimi-20260915-beta2 (v1.0.0-beta.6 -> beta.7)
Runs: release run 35163087056 (v1.0.0-beta.6), all seed native-build legs

## Symptom

Every "Build native * binary via bootstrap-only Rust seed" step in the
v1.0.0-beta.6 release run failed with:

```
SCV-E-ADMISSION: git-event-apply:inventory-publication-failed
✗ native-build failed or binary broken; bootstrap-only Rust seed cannot satisfy release
```

Blocking leg windows-x86_64 failed this way (linux-x86_64 was cancelled
externally before finishing; darwin legs fail later for an unrelated,
still-uninvestigated reason and are non-blocking).

## Root cause

`compile_source_inventory_publish_v1` takes
`file_lock("{root}/publication.lock", 5)` before writing the generation
file and CURRENT pointer. Under the Rust seed, compiled Simple code reaches
runtime services through the SFFI layer
(`src/compiler_rust/runtime/src/value/sffi/file_io/file_ops.rs`). Its
`rt_file_lock`/`rt_file_unlock` had unconditional Windows stubs:

```rust
#[cfg(not(unix))]
{
    let _ = (path, timeout_secs);
    -1
}
```

so on Windows every compiled-code `file_lock` call returned -1 (timeout),
publish returned "", and the admission failed closed. The interpreter-side
implementation (`compiler/src/interpreter_extern/file_io.rs`) and the C
runtime (`src/runtime/platform/platform_win.h`, LockFileEx) were already
correct, which is why host-side unit specs and self-hosted binaries never
reproduced it.

The beta.5 run never reached this wall: cold init failed earlier with
`event-invalid` (fixed by PR #1036). Publication is the next stage.

## Evidence

- CI: run 35163087056 windows-x86_64 job 105020185720 step log.
- Local faithful repro (this host, Windows): seed + exact CI invocation
  (`RUST_LOG=error SIMPLE_BOOTSTRAP=1 native-build --source-dir src
  --entry-closure --entry src/app/cli/bootstrap_main.spl --output ...`)
  failed identically in ~19 min; eprint instrumentation of every publish
  `""` return site narrowed it to the lock branch; the seed's interpreter
  `rt_file_lock` was never entered (no diagnostic lines), isolating the
  SFFI copy.
- After implementing the Windows branch (CreateFileA OPEN_ALWAYS +
  LockFileEx, mirroring platform_win.h), the same repro passes the SCV
  admission.

## Fix

`src/compiler_rust/runtime/src/value/sffi/file_io/file_ops.rs`:
Windows `rt_file_lock` uses CreateFileA + LockFileEx (blocking when
`timeout_secs <= 0`, `LOCKFILE_FAIL_IMMEDIATELY` poll with the deadline
otherwise), returning the HANDLE as the owned descriptor; `rt_file_unlock`
calls UnlockFileEx + CloseHandle. Same contract as the unix flock branch
and the C runtime.

## Follow-ups (not gating)

- `rt_file_copy_create_excl_no_follow` / `rt_file_link_create_excl_no_follow`
  and descriptor read/write in the same SFFI layer still carry
  `cfg(not(unix))` ENOSYS stubs; they are off the SCV path but will bite
  other compiled-code lanes on Windows.
- linux-x86_64 cancellation in run 35163087056 (01:00:55Z) has no in-repo
  explanation (concurrency is cancel-in-progress:false); likely external.
- darwin seed native-build legs fail later and separately; non-blocking.
