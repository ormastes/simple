# native_project codegen: an ambiguous bare function name is left unresolved even when the calling module imports it explicitly

- **Date:** 2026-10-20
- **Status:** open; worked around at the source level in the Phase 4 link-symbols lane (PR `work/phase4-link-symbols`)
- **Where:** `src/compiler_rust/compiler/src/pipeline/native_project/imports.rs:673-691` (import map), consumers in `codegen/common_backend.rs` (`ambiguous_names`)
- **Seen on:** seed `51d63d3f…` (Rust seed, cranelift), Phase 4 full-CLI build of `release_phase3` @ `436f5818df5`

## Symptom

The strict final link (`SIMPLE_NO_STUB_FALLBACK=1`) of the Phase 4 full CLI fails with two
undefined **internal Simple** symbols, both referenced by live code (mold `--gc-sections`,
roots `main`/`spl_main`):

```
mold: error: undefined symbol: min_i64
      referenced by lib__gc_async_mut__gpu__browser_engine__simple_web_html_layout_renderer___simple_web_css_animation_instance_next_ms
mold: error: undefined symbol: _text_list_contains
      referenced by compiler__driver__driver_compile_vhdl_expr___simple_entity_type_declaration_block
```

Both call sites compile to a **bare** symbol, i.e. the native import map produced no mangled
owner for the name.

## Root cause

`imports.rs` builds one process-wide `raw -> mangled` map. When a raw name has more than one
definition in the entry closure it is put in `ambiguous`; a private (`_`-prefixed) name gets no
mapping at all, a public one keeps first-wins "until all consumers check the `ambiguous` set".
Codegen then emits the bare name for the call, which nothing defines.

- `min_i64` is defined in 5 modules (`std.math` plus four private module-local copies in
  `replay/process/checkpoint.spl`, two `debug/remote/exec/uploader.spl`, `wm/wm_optimization.spl`).
  The renderer imports it **explicitly** (`use std.math.{min_i64}`), so the module's own import
  context is sufficient to resolve the owner, but the map is global and the explicit import is
  never consulted.
- `_text_list_contains` is defined in 4 modules; `driver_compile_vhdl_expr.spl` reaches the
  `driver_compile_vhdl_util.spl` copy through a glob import (`use ….driver_compile_vhdl_util.*`).

The interpreter resolves both through per-module import scope, so the defect is native-only and
invisible to `simple test`.

## Workaround landed

Source-level disambiguation only (no compiler change): the four private `min_i64` copies are
renamed `_min_i64` (module-local, never exported), and the vhdl helper is renamed
`vhdl_text_list_contains` across the five `80.driver/driver_compile_vhdl_*.spl` files. This is
a workaround for the resolution rule above, not a fix of it.

## Fix wanted

Resolve a bare call through the calling module's explicit `use` list before falling back to the
global map; a name that is explicitly imported from one module is not ambiguous for that caller.
Glob imports of `_`-private helpers should be a diagnostic, not a silent unresolved symbol.
Until then the strict Stage 4 link is the only gate that sees this class; the non-strict
preflight (`stubs.rs` `internal_missing`) reports it only when the stub lane is enabled.

## Measurement context (same lane)

Found by a strict zero-recompile relink of the kept Phase 4 objects (seed `51d63d3f`, cranelift,
`--cache-dir` copy): with the original entry `src/app/cli/_CliMain/main_and_help.spl` the receipt
read `Incremental: 2765 cached, 3 to compile` / `[native-incremental] 2765 reused / 3 rebuilt`
(18.8 s to link start) and mold reported exactly 151 live undefined symbols — 124 provided by the
Rust runtime staticlib on the Stage 4 lane, 25 `rt_sqlite_*` from objects predating the embedded
backend, and these 2. Switching the entry to the sanctioned `src/app/cli/main.spl` changes the
import map (`Found 2769`, 335 re-exports) and with it `GlobalBuildFingerprint.layout`
(`native_project/mod.rs:1038-1041`, folded into every object key at `:1094`), so the same cache
answers `Incremental: 0 cached, 2769 to compile`: the authorized Stage 4 link is a full recompile
(measured 572 s / 3.7 GB RSS at 8 workers), not a relink.
