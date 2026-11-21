# BUG-RT-TUPLE-LEN-UNBACKED-SEED-20261102

- Symptom: every `bin/simple.exe test <spec>` on Windows release/1.0.0 fails with
  `semantic: unknown extern function: rt_tuple_len` before running a spec.
- Binary: `bin/simple.exe` is the Rust bootstrap seed (self-reports "bootstrap seed only").
- Cause: 9336ac0e56b (2026-10-29) made `env_vars_nilable` in
  `src/lib/nogc_sync_mut/sffi/system_env_core.spl` call `rt_tuple_len`/`rt_tuple_get`,
  which the deployed seed interpreter's extern registry does not back.
- Workaround: `@workaround bug=BUG-RT-TUPLE-LEN-UNBACKED-SEED-20261102` restores the
  direct `rt_env_vars()` return. Native tuple-header projection concern from
  9336ac0e56b is re-opened (it was never execution-verified there).
- Close: deploy a binary registering `rt_tuple_len`/`rt_tuple_get`, restore 9336ac0e56b body.
- Other unbacked use: `src/lib/nogc_sync_mut/sffi/enum_wire.spl` (only if imported on the test path).

## 2026-11-22: workaround removed; it broke native `--parallel` on Windows

- The direct `rt_env_vars()` return was not harmless in native builds. A runtime
  pair is an array-headed heap object (`rt_tuple_new` in
  `src/runtime/runtime_native.c`); native code reads a typed `(text, text)` as two
  inline words. `for (key, value) in snapshot` in
  `src/lib/nogc_sync_mut/io/windows_redirected_process.spl` therefore bound two
  header words, every child environment entry became `=`, and
  `windows_process_request_valid_v1` returned `invalid environment assignment`.
  The runner reported it as
  `owned Windows child admission or collection failed: child admission refused`
  for every file under `--parallel` (rc 1). `--sequential` does not use the owned
  spawn and was unaffected; the interpreter was never affected.
- Evidence (pin-built rung-7 runner, lldb): `windows_process_request_valid_v1`
  returns that text on the first assignment, whose bytes are `=`; the loop's
  disassembly loads `[pair & ~7]` and `[pair & ~7 + 8]` with no `rt_tuple_get`.
- Fix: `env_vars_nilable` again rebuilds language tuples through
  `rt_tuple_len`/`rt_tuple_get`. `C:/dev/seeds/simple-release.exe` and the
  release-tip interpreter (`interpreter_extern/mod.rs`) register both.
- Same destructure, covered by the same owner change:
  `src/lib/nogc_sync_mut/test_runner/aggregate_task_executor.spl` (environment
  digest). The `pair.0`/`pair.1` readers in `src/app/bootstrap_builder/` consume
  the same snapshot; their native behaviour was not measured here.
- Spec: `test/01_unit/lib/sffi/rt_tuple_len_env_vars_spec.spl`. It passes under
  the interpreter before and after, so the native witness is a pin-built probe of
  the same loop, not the spec.
