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
