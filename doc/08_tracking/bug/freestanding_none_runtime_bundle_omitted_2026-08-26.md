# Freestanding `unknown-none` runtime bundle omitted from link

Status: FIXED IN SOURCE; BUILD ADMISSION PENDING
Owner: native-project freestanding linker
Date: 2026-08-26

## Symptom

The no-stub WM showcase target compiles its complete Simple closure for
`x86_64-unknown-none`, accepts `--runtime-bundle simple-core`, and resolves the
archive named by `SIMPLE_SIMPLE_CORE_PATH` / `SIMPLE_CORE_RUNTIME_PATH`, but the
final `ld.lld` command omits that archive. Symbols visibly defined by the
archive (`rt_string_builder_new`, `rt_string_builder_push`,
`rt_string_builder_finish`, `rt_any_ge`, `rt_any_sub`, and
`rt_is_interpreter_runtime`) therefore remain undefined.

The preserved failed-link objects are under
`.simple/native-objects-4p9t9w`. The target simple-core archive is
`build/os/simple-core-none/libsimple_runtime.a`.

## Root cause

`NativeProjectBuilder::link_objects_freestanding` only appended a runtime when
`simpleos_user_runtime_paths()` returned a full SimpleOS sysroot tuple. That
helper intentionally rejects `TargetOS::None`. The ordinary
`selected_runtime_library()` result used by hosted builds was never consulted
or appended by the freestanding path.

## Source fix

The freestanding linker now resolves the selected runtime when no SimpleOS
sysroot tuple owns the link and appends it in both direct-`ld.lld` and
compiler-driver command construction. It also applies the existing
native-all rejection before linking. No hosted or removed runtime fallback is
introduced.

## Remaining distinct work

After the archive is actually linked, any residual undefined symbols must be
classified separately:

- ABI functions genuinely missing from pure Simple core, including
  `rt_string_parse_int` and `rt_string_is_digit`.
- Host-only backend functions retained by module-granular entry closure
  (CUDA, Metal, ROCm, and host GPU queue symbols). The preferred correction is
  target-aware closure pruning or a real unavailable-backend authority, not
  fabricated success stubs.
- The unresolved `gc_env_get` alias in
  `src/lib/gc_async_mut/env/variables.spl` is repaired in source by routing
  directly through canonical `std.io_runtime.env_get_opt`.
- Bare-metal math/compiler builtins such as `ceil`.

## Admission criterion

A fresh no-stub WM build must produce a regular x86-64 ELF from the frozen
source identity, with the selected simple-core archive present on the link
line and no undefined symbols. Headless QEMU/container Vulkan capture remains
the runtime acceptance step after that build succeeds.
