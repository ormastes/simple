# Frozen stage2 inlines std.env.env_get with the boxed text in rcx while the C rt_env_get takes (ptr, len)

- **ID:** stage2_inline_env_get_boxed_extern_abi_2026-11-03
- **Priority:** P1 (phase 3: stage3 codegen phase dies in ucrtbase memcpy)
- **Status:** open. Source workaround landed in `driver_aot_native_output.spl` (use the imported
  `env_get_nullable`) and `driver_bootstrap.spl` (local non-inline `env_get` over `io_runtime.env_get_nullable`).

## Symptom
Stage3 hello build (HIR cache off, MIR patched) reaches `phase=native_compile` and dies with 0xC0000005 in
`ucrtbase.dll!memcpy` <- `rt_env_get+65` <- `CompilerDriver._compile_to_native_with_backend_session`
(minidump `veh_89604.dmp`): `memcpy(out, 0x1d564361ff1, 0x1740480)`.

## Root cause
The C runtime declares `int64_t rt_env_get(const uint8_t* key_ptr, uint64_t key_len)` and copies `key_len`
bytes from `key_ptr`. Every stage2-built object that calls it from its OWN module passes
`(rt_string_data(k), rt_string_len(k))` (22 combined3 objects checked). But `std.nogc_async_mut.env.variables`
declares `@always_inline fn _env_get_raw(key) -> rt_env_get(key)` against `extern fn rt_env_get(key: text)`,
and when the frozen stage2 inlines that into a driver module it emits ONE argument: `rcx = rt_string_new_literal(...)`
(the boxed text) with `rdx` left over from the previous call (`0x16`, then clobbered). OLD objects
`aot-ba4264...` (driver_aot_native_output, 1 site: `env_get("SIMPLE_M4_WORK_RECEIPT")`) and
`aot-f94507...` (driver_bootstrap, 9 sites: `use std.env.{env_get}`) carry that shape.

## Workaround
Route those modules' env reads through the non-inline `std.nogc_sync_mut.io_runtime.env_get_nullable`
wrapper, which passes `(data, len)`. Link-level interim (not landed): `llvm-objcopy --redefine-sym
rt_env_get=rt_env_get_value` on copies of the two objects (`rt_env_get_value(int64_t boxed)` is the C
entry point for the boxed convention); `s3_fable4.exe` passed this phase with it.

## Removal condition
A stage2 whose inliner expands `text` extern arguments to `(data, len)` across module boundaries.
