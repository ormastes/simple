# JIT: `env_set as io_runtime_env_set` stays unresolved and rendering_gui_core runs fully interpreted

- **Filed:** 2026-10-05
- **Area:** `src/lib/nogc_sync_mut/env/variables.spl`, plus the same pattern in
  `src/lib/nogc_sync_mut/sffi/system.spl` and `src/lib/nogc_async_mut/io/mod_stub.spl`
- **Status:** FIXED 2026-10-05

## Symptom

`examples/06_io/ui/rendering/rendering_gui_core.spl` at 3840x2160 under the JIT:

```
[jit-fallback] unresolved external symbol 'io_runtime_env_set': whole module
dropped to the interpreter (expect ~100-1000x slowdown).
```

It took 774 s wall and 3.44 GB RSS.

## Root cause

`env/variables.spl` defines its own `env_set` and imported the io_runtime one
as `use std.io_runtime.{env_set as io_runtime_env_set}`. In the flattened unit,
an aliased import of a name that the importing module also defines is left
unresolved. This is the same collision that
`src/lib/nogc_sync_mut/io_runtime.spl:443` already documents, and the reason
the unique `env_set_process` / `cwd_process` wrappers exist.

`sffi/system.spl` and `io/mod_stub.spl` used the same pattern for `cwd`
(`cwd as io_runtime_cwd` while defining `fn cwd()`).

## Fix

All three call the unique wrappers instead: `env_set_process` and
`cwd_process`. Their bodies are identical to `env_set` and `cwd`.

## Evidence

rendering_gui_core, 3840x2160, same seed and tree:

| | wall | max RSS | mode |
|---|---|---|---|
| before | 774 s | 3.44 GB | interpreted |
| after | 3.9 s | 0.77 GB | JIT |

The two PPM captures are byte-identical (`cmp`).

Specs, both in `test/01_unit/lib/nogc_sync_mut/io_runtime_alias_collision_spec.spl`:

- **repro:** `env_set` round-trip through `env.variables`.
- **generalization:** none of the wrappers that define `env_set`/`cwd` alias the same io_runtime name. This includes a positive-control read.

Root seed limitation (aliased import of a locally redefined name) is not
fixed here. This change follows the existing repo precedent.
