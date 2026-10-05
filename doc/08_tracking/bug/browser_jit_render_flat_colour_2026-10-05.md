# Browser engine never JIT'd; once it did, real pages rendered as one flat colour (2026-10-05)

Status: FIXED in branch `work/browser-style-jit-font` (4 roots), host macOS arm64.

## Symptom

Every browser render (`render_html_to_pixel_array`, the static lane) ran in the
seed **interpreter**: news.ycombinator.com took ~35 s of style+layout and
~190 s overall. The `[jit-fallback]` / `[INFO] JIT ... falling back` lines named
the cause, one root at a time.

## Roots (in the order they surfaced)

1. **Codegen panic `no entry found for key`** in `Engine2D.invalidate_damage_mirror`,
   `read_pixels_region`, `read_pixels_damaged`
   (`closures_structs.rs:3016`, `ctx.runtime_funcs["rt_method_not_found"]`).
   The erased-receiver vtable switch synthesizes its miss arm as a call to
   `rt_method_not_found` from a `MethodCallStatic`, so the symbol never reached
   `referenced_call_names`; it was declared only when the module also contained
   a `BuiltinMethod`. Fix: codegen root in `common_backend.rs`
   (`runtime_symbol_is_codegen_root`), test `vtable_switch_miss_symbol_is_retained`.
2. **`AArch64 direct call is 348518736 bytes away`** (JIT panic). The vendored
   cranelift-jit contiguous 128 MiB code arena
   (`jit_aarch64_branch_relocation_out_of_range_abort_2026-09-05.md`) was gated
   to `target_os = "linux"`; on Apple Silicon JIT code came from the heap. Fix:
   enable it on macOS (`vendor/cranelift-jit/src/memory.rs`, checksum refreshed).
   Measured high-water: 22.6 MiB of the 128 MiB arena for the browser program.
3. **Shared default Style.** With the JIT running, real HN rendered as one flat
   colour (`0xFFFFFF03`). `renderer_default_style()` memoised one `Style`
   assuming copy-on-bind; compiled code treats `class` as an identity type
   (`copy_if_value_type` copies `struct` only), so every node's
   `var st = renderer_default_style()` aliased one object. Fix: build per call.
4. **`argb` name collision.** `fg` came out as `3` instead of `0xFF000000`: the
   engine's `argb(r,g,b)->u32` and `common/render_scene/scene.spl`'s
   `argb(a,r,g,b)->i32` are co-compiled and a call with untyped literals bound
   to the scene one. Fix: rename the engine's to `web_argb`.

## JIT reproducer for 3 (the spec runner itself falls back to the interpreter,
so a `run` probe is the reproducer; interpreter prints a.fs=16, JIT printed 99)

```simple
use std.gc_async_mut.gpu.browser_engine.simple_web_html_layout_renderer_style.{renderer_default_style}
fn main():
    val a = renderer_default_style()
    var c = renderer_default_style()
    c.font_size = 99
    print "a.fs={a.font_size}"   # must be 16
```

Specs: `test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_style_jit_identity_spec.spl`
(contract: fresh default per call, earlier nodes keep their style, `web_argb`
packing) and the Rust unit test above.

## Still open (not fixed here)

- Other co-compiled duplicate names still warned on the browser program:
  `be_dom_find_by_id`, `glyph_scale`, `hex_to_int`, `parse_hex_color`,
  `resolve_style`, `wrap_line_end`, `dir_remove_all`. Pixels are identical on
  the four fixtures, but any of these can mis-bind the same way as `argb`.
- `var q = p` on a `class` aliases under JIT and copies under the interpreter
  (`doc/07_guide/language/value_semantics_by_engine.md`); engine code written
  against interpreter semantics may hide more aliasing.
- JIT compile of the whole browser program costs ~4-7 min and ~4.8 GB RSS at
  startup on this host; render itself is ~1 s.
- Live https fetch fails under JIT (`h1: TLS read failed or timed out`) and
  works under `SIMPLE_EXECUTION_MODE=interpreter` (net lane).
