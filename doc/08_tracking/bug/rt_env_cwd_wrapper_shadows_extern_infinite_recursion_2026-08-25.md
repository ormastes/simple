# `rt_env_cwd` Simple wrapper shadowed the runtime extern → infinite recursion (2026-08-25)

**Status:** FIXED in this change. **Symptom:** every `bin/simple todo-scan` on clean `origin/main`
died with `error: stack overflow: recursion depth 1000 exceeded limit 1000 in function 'rt_env_cwd'`.

## Cause
- `src/lib/nogc_sync_mut/io_runtime.spl:67` declares the runtime symbol:
  `extern fn rt_env_cwd() -> text?`, and `cwd()` (`:338`) calls it.
- `src/lib/nogc_sync_mut/env/types.spl:16` defined a **Simple function of the same name**:
  `fn rt_env_cwd() -> text: io_runtime_cwd()` — i.e. it called `io_runtime.cwd()`.

The interpreter resolves functions by NAME across co-compiled modules, so `io_runtime.cwd()` →
`rt_env_cwd()` bound to the Simple wrapper → `io_runtime.cwd()` → … until the depth limit.
A wrapper must never take the name of the `rt_*` symbol it wraps.

## Fix
`env/types.spl` now declares the extern itself (matching `shell.spl`, `sys/env.spl`,
`tooling/config_env.spl` and `io_runtime.spl`, where `rt_env_cwd` is always an extern), and the two
`get_current_dir()` callers (`nogc_sync_mut/env/platform.spl:324`,
`nogc_async_mut/env/platform.spl:335`) unwrap the optional explicitly. The exported name is
unchanged, so `test/01_unit/lib/nogc_sync_mut/env_platform_process_owner_spec.spl`, which pins both
the import line and the export list textually, still holds.

## Evidence
`bin/simple todo-scan` in a clean `origin/main` worktree: crash → `Scan complete: 239 TODOs found`.
