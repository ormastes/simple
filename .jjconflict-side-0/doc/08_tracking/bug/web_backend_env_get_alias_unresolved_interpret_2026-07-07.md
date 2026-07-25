# Interpreter: `env_get as web_backend_env_get` re-export alias unresolved — chromium WebRenderBackend facade crashes E1002

Date: 2026-07-07
Status: fixed
Severity: P2
Related: web_render_backend (`--web-engine chromium` facade), family of
`interp_module_alias_time_shadowed_builtin_2026-07-02.md` (interpreter
module-alias resolution gaps)

## Symptom

`src/lib/gc_async_mut/gpu/browser_engine/web_render_backend.spl` imports:

```simple
use std.gc_async_mut.io.mod_stub.{env_get as web_backend_env_get}
```

`mod_stub` re-exports `env_get` from `env_ops` (itself layered:
`std.gc_async_mut.io.env_ops` -> `export use std.nogc_async_mut.io.env_ops.*`
-> ... -> `std.nogc_sync_mut.io.env_ops`). Under
`SIMPLE_EXECUTION_MODE=interpret`, any call through the aliased name
`web_backend_env_get` (used by `_chromium_tmp_dir`, `_env_or`, `_repo_root`,
etc. — i.e. any call to `render_html_to_pixels` on the chromium engine)
crashes:

```
error[E1002]: function `web_backend_env_get` not found
  = help: check the function name or import the module that defines it
```

This is a facade-level bug, unrelated to `ui.browser`: it reproduces with
zero browser code, using only `web_render_backend` directly.

## Repro (verified 2026-07-07, facade-only, zero browser code)

```simple
use std.gc_async_mut.gpu.browser_engine.web_render_backend.{web_render_backend}

fn main():
    val backend = web_render_backend("chromium", 4, 4)
    val pixels = backend.render_html_to_pixels("<html><body>hi</body></html>")
    print "pixels len: {pixels.len()}"
```

```bash
SIMPLE_EXECUTION_MODE=interpret bin/simple run probe_env_get2.spl
# error[E1002]: function `web_backend_env_get` not found
```

Note: constructing the backend (`web_render_backend("chromium", 4, 4)`)
succeeds — the crash only fires on the first call that reaches
`_chromium_tmp_dir`/`_env_or`/`_repo_root`, i.e. the first
`render_html_to_pixels` call on the chromium engine.

## Impact on backend-isolation Gap B (`ui.browser` `--web-engine`)

`src/app/ui.browser/backend.spl`'s `browser_backend_chromium_pixel_artifact`
calls `web_render_backend(WEB_RENDER_ENGINE_CHROMIUM, ...).render_html_to_pixels(...)`,
so under interpret mode selecting `--web-engine chromium` (or constructing a
`BrowserBackend` with `web_engine: "chromium"` and rendering a frame) hits
this same E1002 crash. This is loud and immediate — there is no silent
fallback to a zero-length pixel buffer or to the `pure_simple` output. Prior
docstrings in `backend.spl` claimed the chromium lane "returns an empty
pixel buffer ... never silently substituted" on failure; that description
was inaccurate for the interpreter (it never reaches a normal
success/failure return at all — it crashes at the alias-resolution step)
and has been corrected to describe the E1002 crash directly, citing this
record.

## Family

Same root-cause family as
[`interp_module_alias_time_shadowed_builtin_2026-07-02.md`](interp_module_alias_time_shadowed_builtin_2026-07-02.md)
and
[`interp_io_runtime_env_get_option_text_corruption_2026-06-19.md`](interp_io_runtime_env_get_option_text_corruption_2026-06-19.md):
the interpreter's module-alias / re-export resolution does not reliably
thread renamed imports through multi-hop `export use module.*` chains,
particularly for `env_get`-shaped stdlib entry points.

## Fix direction

- Resolve `use X.{name as alias}` through multi-hop `export use module.*`
  re-export chains in the interpreter's module resolver (the general fix,
  benefits the whole family), or
- De-alias `web_render_backend.spl`'s facade: import `env_get` directly from
  a single-hop module (skip the `mod_stub` indirection) so the interpreter's
  resolver has a direct binding to find, or
- Compile the chromium lane ahead-of-time (native/compiled execution mode)
  until the interpreter gap is fixed, and gate `--web-engine chromium` on
  execution mode with a clear error pointing here.

Until fixed, the chromium lane is native/compiled-mode only; interpret mode
fails loudly (E1002) rather than silently degrading.

## Fix

2026-07-08: `web_render_backend.spl` now imports `env_get` directly from the
env facade instead of aliasing it through `mod_stub`. Native CPU-SIMD scale
evidence no longer falls back on `web_backend_env_get` lowering and
`sh scripts/check/check-cpu-simd-render-scale-contract.shs` passes at 4K and 8K.
