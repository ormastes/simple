---
title: "simd_config_mode() returns nil instead of the documented \"auto\" default when SIMPLE_2D_SIMD is unset"
status: resolved
date: 2026-08-07
resolved_date: 2026-08-07
---

## Summary

`pub fn simd_config_mode()` in
`src/lib/nogc_sync_mut/gpu/engine2d/simd_kernels.spl:346-350` is documented
(comment above it, line 338-345, and in `src/app/test/...` usage) to default
to `"auto"` when the `SIMPLE_2D_SIMD` env var is unset. In practice it
returns `nil`, not `"auto"`, whenever the variable was never set (or was
explicitly unset via `env_unset`/`rt_env_remove`).

```
346  pub fn simd_config_mode() -> text:
347      val raw = rt_env_get("SIMPLE_2D_SIMD")
348      if raw == "":
349          return "auto"
350      raw
```

`rt_env_get` returns `nil`, not an empty `text`, for an unset variable — this
is the same divergence already handled correctly elsewhere in the codebase,
e.g. `src/lib/nogc_sync_mut/env/variables.spl:11-22`:

```
fn env_get(key: text) -> text:
    val value = rt_env_get(key)
    if value == nil:
        ""
    else:
        value
```

`simd_config_mode()` only checks `raw == ""`, which is never true for the
nil case, so the function falls through to `raw` (nil) instead of the
`"auto"` default. Any caller that checks `simd_config_mode() == "auto"` (or
relies on a non-nil `text` return, per the declared `-> text` signature) sees
this break silently.

## Evidence

Reproduced directly via
`test/01_unit/lib/gpu/engine2d/simd_kernels_spec.spl`, describe block
`"simd_config_mode"`:

```
it "F6: empty/unset SIMPLE_2D_SIMD defaults to auto":
    env_unset("SIMPLE_2D_SIMD")
    expect(simd_config_mode()).to_equal("auto")
```

Fails with `expected nil to equal auto` under `bin/simple test
test/01_unit/lib/gpu/engine2d/simd_kernels_spec.spl --no-cache
--no-cover-check` (interpreter lane). The sibling case
`"SIMPLE_2D_SIMD=off is honored verbatim"` (which sets a real value first via
`env_set`) passes, confirming the non-nil path is fine and the defect is
specific to the unset/nil path.

## Fix (applied)

`simd_config_mode()` now carries the same nil guard as `env_get`, in
`src/lib/nogc_sync_mut/gpu/engine2d/simd_kernels.spl:346-350`:

```
pub fn simd_config_mode() -> text:
    val raw = rt_env_get("SIMPLE_2D_SIMD")
    if raw == nil or raw == "":
        return "auto"
    raw
```

## Resolution evidence

No spec changes were needed — the existing `simd_config_mode` describe block
in `test/01_unit/lib/gpu/engine2d/simd_kernels_spec.spl` already asserted the
correct (previously-RED) behavior. With the nil guard applied, `bin/simple
test test/01_unit/lib/gpu/engine2d/simd_kernels_spec.spl --no-cache
--no-cover-check` shows all three `simd_config_mode` its green:

```
✓ F6: empty/unset SIMPLE_2D_SIMD defaults to auto
✓ F6: SIMPLE_2D_SIMD=off is honored verbatim
✓ F6: an explicit ISA name passes through unmodified
```

Full-file run: `Results: 45 total, 44 passed, 1 failed` — the sole remaining
failure (`uses the cross-mode return-array span bridge for backend fills`) is
unrelated to env handling / `simd_config_mode` and pre-exists this fix; out
of scope here.

## Unblock condition (met)

Land the nil guard above (or route through `std.env.variables.env_get_or`,
which already has it), then the two RED its in the `simd_config_mode`
describe block in `test/01_unit/lib/gpu/engine2d/simd_kernels_spec.spl` go
green with no further spec changes. Done.
