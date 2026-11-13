# sffi_vulkan.spl calls env_get without importing it; JIT demotes to the interpreter

- **ID:** sffi_vulkan_env_get_unimported_jit_demotion_2026-11-13
- **Status:** FIXED 2026-11-13
- **Severity:** P3
- **Found by:** UI batch B, 8K frame-switch gate run
- **Owner:** Vulkan / engine2d lane (file not edited by the finder)

## Evidence

`src/lib/nogc_sync_mut/gpu/engine2d/sffi_vulkan.spl:1168` reads
`(env_get("SIMPLE_VK_READBACK") ?? "") == "native"`. The file's `use` lines
do not import `env_get`.

Running any closure that pulls this module in JIT mode on the Rust seed
(release/1.0.0 `35144b7f5e93`), for example
`test/05_perf/graphics_2d/bench_web_draw_ir_8k_frame_switch.spl`:

```
[engine-demotion] reason=jit-compile-error detail=HIR lowering error:
ambiguous call to `env_get`: 3 co-compiled definitions
(src/lib/nogc_async_mut/env/variables.spl,
 src/lib/nogc_sync_mut/io/env_ops.spl, src/lib/nogc_sync_mut/io_runtime.spl)
and `src/lib/nogc_sync_mut/gpu/engine2d/sffi_vulkan.spl` neither defines nor
imports it
[INFO] JIT compilation failed, falling back to interpreter
```

## Impact

Every program whose closure includes the engine2d Vulkan sffi module silently
runs in the interpreter when JIT was requested. This is what currently keeps
the 8K frame-switch lane from producing an admissible JIT row.

## Fix direction

Import one `env_get` explicitly in `sffi_vulkan.spl` (check which of the three
the interpreter resolves today and import that same definition so behaviour
does not change), then re-run
`sh scripts/check/check-web-draw-ir-8k-frame-switch.shs`, which now fails
closed on a demotion line.

## Resolution (2026-11-13)

`sffi_vulkan.spl` now imports `env_get` from `std.io_runtime`. That is the public, exported
definition that the other engine2d files already import, and every candidate returns `""` when
the variable is unset, so behaviour is unchanged.

Evidence comes from a JIT probe, run with `--mode=jit` on the seed carrying #8785. The probe
pulls in `sffi_vulkan`, `nogc_async_mut/env/variables` and `nogc_sync_mut/io/env_ops`, so all
three `env_get` definitions are compiled together.

- Before the fix: `[engine-demotion] reason=jit-compile-error ... ambiguous call to env_get: 3 co-compiled definitions`.
- After the fix: there is no jit-compile-error demotion, `vulkan_sffi_native_readback_opt_in()`
  returns `false` when unset, and it returns `true` with `SIMPLE_VK_READBACK=native`.

Not covered here:
- The 8K bench still also demotes with `reason=hybrid-interp-splice`, because of unregistered
  process/file externs (the caret-392 class). That is separate from this bug.
- A side finding: in the probe's entry file, `use std.io_runtime.{env_get_or}` did not select
  that definition, and the call stayed "ambiguous ... `<entry file>` neither defines nor imports
  it". Library modules do resolve their selective imports.
