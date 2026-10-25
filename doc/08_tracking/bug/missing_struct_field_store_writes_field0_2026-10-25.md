# A store to a field the struct lacks writes field 0 (CompileOptions.mode)

- **Status:** source fixed (the nonexistent field is no longer used). The
  compiler now fails closed in `resolve_field_index`. That change takes effect
  only after a Stage 2 rebuild, and its whole-tree impact has not been
  measured.
- **Symptom (Phase 3 Stage 3 hello world):** the `run
  src/app/cli/native_build_worker.spl` child printed `panic: ` with an empty
  message and exited 1. The parent re-panicked.

## Root cause

`CompileOptions` (`src/compiler/00.common/driver_compile_options.spl`) has no
`target_opt_ctx` field. The code still used one:

- stores of `options.target_opt_ctx = …`:
  - `src/app/io/_CliCompile/compile_targets.spl` (two, about :1472 and :1527 on release/1.0.0; :1538 and :1600 in the bootstrap base d3fc04205cf);
  - `src/app/io/_CliCompile/compile_opt_and_driver.spl:153`, on the `compile` path;
  - `src/app/io/_CliCompile/native_build.spl:720` and `:761`;
- a read of `ctx.options.target_opt_ctx`:
  - `src/compiler/80.driver/driver_aot_native_output.spl` (about :2630 on release, :2762 in the base).

MIR `resolve_field_index` (`src/compiler/50.mir/_MirLowering/function_lowering.spl`)
found the `CompileOptions` layout but no field with that name. It then
returned its "default fallback" index 0, so the store overwrote field 0,
`mode: CompileMode`, with a `TargetOptContext` pointer.

`CompileContext.create` (`driver_types.spl:584`) calls `options.mode.to_text()`.
None of the `rt_enum_check_variant` arms match a non-enum word, so it fell
through to `rt_panic("")`.

## Evidence

gdb on the exact worker argv and environment, captured with an LD_PRELOAD
shim (stage3 `simple.r7`, sha c145d410):

- The `CompileMode.Aot` enum built by `rt_enum_new` (`0x…6431`, disc=2) was
  never overwritten.
- `_cli_native_build` at `0x3039368..74`: `ldr x12, [_nb_target_opt_ctx]` and
  `str x12, [options + 0]`, immediately before `compileoptions_normalize_mir_optimization`.
- The `mode` word from normalize down to `CompileContext.create` was
  `0x…e141`, which is not a registered enum (`rt_enum_discriminant` = -1).
- Frame-pointer backtrace at `exit`:
  `spl_panic` < `rt_panic` < `CompileMode.to_text` < `CompileContext.create` <
  `compiler_driver_create` < … < `_cli_native_build` < `run_native_build_worker_entry`.

## Fix

- **Source:** drop all five stores, the unused locals and imports, and the
  `target_opt_ctx` parameter of `cli_compile_pure_simple`. Every caller passed
  `target_opt_context_default()` to that parameter. Read `target_opt_context_default()` at the group-pair call.
  That is the value the CLI always computed, so behaviour is unchanged.
  `CompileOptions` lives in `00.common` and cannot import the `60.mir_opt`
  `TargetOptContext` type, so adding the field would invert the layering.
- **Compiler:** `resolve_field_index` now calls `error_fatal("no field
  '<f>' on '<module::S>'")` instead of returning 0, but only when the EXACT
  module-qualified layout was found and no tier names the field.
  - The bare-name and `struct_value_syms` tiers can hold another struct of the
    same name: `module_lowering.spl` overwrites `struct_field_order[name]`
    without the conflict check. They therefore keep the old silent fallback.
  - An unknown type, and the `field_map` tier, still fall back to index 0.
  - Whole-tree impact will be visible at the next Stage 2 rebuild.

Spec: `test/01_unit/compiler/50.mir/missing_struct_field_lowering_spec.spl`
(MIR lowering through the interpreter).
