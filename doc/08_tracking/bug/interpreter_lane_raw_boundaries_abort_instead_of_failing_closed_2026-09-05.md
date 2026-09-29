# Interpreter lane: three raw SFFI boundaries abort (or fabricate) instead of returning their documented failure sentinel

Date: 2026-09-05
Status: OPEN
Area: compiler/interpreter externs, SFFI
Found by: `test/03_system/plan_acceptance/sffi_universal_admission_next_spec.spl`

## Summary

Three raw boundaries have a documented fail-closed contract on the Simple side,
but the seed interpreter lane does not honour it. Two abort the whole
interpreter; one fabricates a plausible-looking handle. In every case the
documented failure value is unobservable to a caller in that lane, so the
Simple-side `Result`/sentinel contract is dead code there.

| boundary | documented failure | interpreter lane actually does |
|---|---|---|
| `spl_dlopen` (registered at `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:2635` -> `wsffi::spl_dlopen`) | non-positive handle -> `Err("E-SFFI-001: failed to load provider: …")` (`src/lib/nogc_sync_mut/sffi/dynamic.spl:56`) | raises `spl_dlopen failed for '<path>'` and aborts |
| `rt_file_mmap_read_bytes` | nil -> `Err("file mmap read failed: …")` (`src/lib/nogc_sync_mut/io/file_ops.spl:199`) | raises `rt_file_mmap_read_bytes failed: No such file or directory (os error 2)` and aborts |
| `rt_webgpu_create_surface` (`src/compiler_rust/compiler/src/interpreter_extern/gpu.rs:2937`) | `WEBGPU_INVALID_HANDLE = -1` (`src/runtime/hosted/webgpu.rs:52`) | returns `Value::Int(0)` — a plausible handle, not the sentinel |

## Why it matters

`0` from `rt_webgpu_create_surface_fn` is indistinguishable from a real surface
handle at the call site, which is the exact "never manufacture a success-shaped
value" failure the SFFI universal-admission plan exists to remove
(`doc/03_plan/compiler/sffi/sffi_universal_admission_next_2026-08-25.md`). The
two aborting boundaries are worse than a wrong value: no caller can fail closed
at all.

## Current mitigation (pure Simple, landed 2026-09-05)

Callers now reject inputs that can never succeed before entering the raw
boundary, and normalise the WebGPU result:

- `src/lib/nogc_sync_mut/sffi/dynamic.spl` `_sffi_dlopen_checked` — empty path,
  or a path (containing `/`) whose artifact is absent, returns `Err`. Bare
  sonames still reach the loader's own search path.
- `src/lib/nogc_sync_mut/io/file_ops.spl` `file_mmap_read_bytes` / `file_mmap`
  — empty or non-existent path (and non-positive extent / negative offset for
  `file_mmap`) fail closed with `Err` / `-1`.
- `src/lib/nogc_sync_mut/gpu/engine2d/webgpu_sffi.spl`
  `webgpu_sffi_create_surface` — normalises any non-positive provider result to
  `WEBGPU_INVALID_HANDLE`, and short-circuits when the provider is unavailable.

These are workarounds at the caller, not fixes at the boundary. A path that
exists but is unreadable, or a genuinely failing provider, still aborts.

## Unblock condition

The seed's interpreter extern dispatch must return the documented sentinel /
nil for these three symbols instead of raising, and
`rt_webgpu_create_surface_fn` must return `-1`, not `0`. Once that lands, the
caller-side existence probes above can be removed.
