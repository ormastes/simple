# Frozen stage2 inlines std.env.env_get with the boxed text in rcx while the C rt_env_get takes (ptr, len)

- **ID:** stage2_inline_env_get_boxed_extern_abi_2026-11-03
- **Priority:** P1 (phase 3: stage3 codegen phase dies in ucrtbase memcpy)
- **Status:** fix-implemented-verification-pending (2026-11-07, re-scoped; see "Root cause (re-scoped)"). Source workaround landed in `driver_aot_native_output.spl` (use the imported
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

## Root cause (re-scoped 2026-11-07)
Not an inliner defect. The current tree has no cross-module body inliner (the MIR
`ModuleInliner` is per-module, and it preserves the `(ptr, len)` split when it splices a
same-module `@always_inline` wrapper). The one-word call comes from the LLVM backend alias
in `MirToLlvm` (`src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl`, the
`call_func_name` chain): an importer references the provider `env_get` by its bare name,
and the backend rewrote `env_get` to `@rt_env_get` while forwarding the caller's single
boxed text word. MIR's text-extern split is keyed on `rt_env_get`, so it never applied to
the alias. Result: `rt_env_get(handle, <stale rdx>)` -- exactly the observed rcx/rdx shape,
and it looks inlined because the caller calls `rt_env_get` directly.

## Fix
A one-word `env_get` callee now routes to the boxed entry `rt_env_get_value(i64)` (same
as the existing one-word `rt_env_get` guard; Cranelift already had that guard).
Spec: `test/01_unit/compiler/mir/inline_text_extern_abi_spec.spl` (bare alias with literal
and variable keys -- RED before, GREEN after; plus inlined plain/unsafe wrappers and a
direct call, which keep `(ptr, len)`).

Verification pending: a stage2 rebuilt from this source must be re-run on the stage3 /
phase-4 group E path before the source workarounds are removed.
