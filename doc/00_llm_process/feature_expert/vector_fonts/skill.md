# Vector Fonts Feature Expert

## Role

Own feature-specific process knowledge for the vector-font rendering
pipeline: sfnt/TrueType outline decode -> rasterization -> glyph caching ->
compositing into DrawIR/Engine2D pixel buffers, across both the hosted
(interpreter/JIT) and SimpleOS freestanding native-build lanes (cranelift,
`x86_64-unknown-none`, `--entry-closure --mode dynload`). The freestanding
lane has repeatedly exposed silent-miscompile landmine classes that do NOT
reproduce hosted — this entry keeps the avoidance recipes in one place
instead of rediscovering them per glyph bug.

## Pipeline Links

- [verify skill](../../../../.claude/skills/verify/SKILL.md)
- [impl skill](../../../../.claude/skills/impl/IMPL.md)

## Feature Links

- Outline decode: [src/lib/common/encoding/sfnt_glyf.spl](../../../../src/lib/common/encoding/sfnt_glyf.spl)
  (`sfnt_rasterize_codepoint_parts`, `sfnt_rasterize_glyph_index_parts`,
  `sfnt_blob_glyph_exists` — flat cross-module tuple-returning API).
- Rasterizer: [src/lib/nogc_sync_mut/sffi/spl_fonts.spl](../../../../src/lib/nogc_sync_mut/sffi/spl_fonts.spl)
  (`FontRasterizer._rasterize_selected_outline`, `.rasterize_glyph_index`) —
  consumes the sfnt tuple API, caches by `font_cache_identity`. Note: 3
  near-duplicate copies exist across sync tiers (`nogc_sync_mut/sffi`,
  `nogc_sync_mut/ffi`, `nogc_async_mut/sffi`) — the SimpleOS desktop kernel
  path is `nogc_sync_mut/sffi/spl_fonts.spl`.
- Config/policy: [src/lib/nogc_sync_mut/text_layout/font_types.spl](../../../../src/lib/nogc_sync_mut/text_layout/font_types.spl)
  (`FontExecutionPolicy`, `font_render_config_valid`, `font_execution_plan`,
  `draw_text_configured`).
- Renderer: [src/lib/nogc_sync_mut/text_layout/font_renderer.spl](../../../../src/lib/nogc_sync_mut/text_layout/font_renderer.spl)
  — convergence stage between the rasterizer and Engine2D/DrawIR below.
- Engine2D/DrawIR convergence: bitmap fallback path
  [src/lib/gc_async_mut/gpu/engine2d/glyph.spl](../../../../src/lib/gc_async_mut/gpu/engine2d/glyph.spl)
  (`render_text_to_buffer`, file-local `_e2d_char_from_code`); execution-
  target selection
  [src/lib/gc_async_mut/gpu/engine2d/engine.spl](../../../../src/lib/gc_async_mut/gpu/engine2d/engine.spl)
  (`engine2d_default_font_config_for`).
- Baremetal chrome consumer: `_px_draw_text` in
  [src/lib/common/ui/window_scene_draw_ir.spl](../../../../src/lib/common/ui/window_scene_draw_ir.spl)
  — the pixel-buffer text blitter every SimpleOS WM chrome route funnels
  through.
- Related: [backend](../../layer_expert/backend/skill.md) layer expert
  (codegen root causes) and [wm_gui_window_drawing](../wm_gui_window_drawing/skill.md)
  feature expert (Aqua theme + chrome consumer of this pipeline).

## Native-Lane Landmine Classes (2026-07-19 rasterizer campaign)

Six boring-construct recipes, backed by 4 filed compiler bugs (recipes 2-4
share one doc), all specific to `--target x86_64-unknown-none
--entry-closure --mode dynload` (cranelift); none reproduce under the
hosted interpreter/JIT. Prefer the boring form over a clever one in any
code that must run on this lane:

1. **Tuple spill clobbered across an intervening call** —
   [native_tuple_spill_clobber_across_call_2026-07-19.md](../../../../doc/08_tracking/bug/native_tuple_spill_clobber_across_call_2026-07-19.md).
   A stack-spilled tuple's element read, taken after a call happens in
   between, can silently return bytes from the callee's own tuple
   construction (wild pointer — e.g. reading a cache-identity string as a
   metrics array). Recipe: snapshot every `parts.N` into a local
   immediately after producing the tuple, before ANY further call — see
   `_rasterize_selected_outline` / `rasterize_glyph_index`.
2. **`char_code_at` returns a tag-shifted value** —
   [native_char_code_at_tag_shift_2026-07-19.md](../../../../doc/08_tracking/bug/native_char_code_at_tag_shift_2026-07-19.md).
   The same boxed value reads as `v`, `v>>3`, or `v&7` depending on read
   site — a cancel-and-"work"-by-coincidence trap; don't compensate at
   call sites. Recipe: call `.bytes()` once and index the byte array
   instead of calling `char_code_at` per character — see the
   `text_bytes = text_value.bytes()` pattern in `_px_draw_text` and in
   `render_text_to_buffer` (glyph.spl).
3. **Byte-to-char mapping needs its own file-local copy** — same doc as
   above. Don't call a shared/cross-module `char_from_code`-style helper;
   keep a small file-local byte-to-text mapper next to each consumer —
   see `_e2d_char_from_code`, a private `fn` in the same file as
   `render_text_to_buffer` (glyph.spl), not an imported utility.
4. **`u8` compares/bit-tests are unreliable — hoist to `i64`** — suspected
   `u8 !=` miscompile, tracked inside the char_code_at doc above. Recipe:
   widen to `i64` before comparing/bit-testing a byte, rather than
   testing the `u8` directly — see the `i64 bit-test + byte accessor`
   comment at the top of `_px_draw_text` (window_scene_draw_ir.spl:259).
5. **String interpolation silently emits verbatim source for a nested
   if/else hole** —
   [native_string_interp_nested_if_verbatim_2026-07-19.md](../../../../doc/08_tracking/bug/native_string_interp_nested_if_verbatim_2026-07-19.md).
   No diagnostic; `{if cond: 1 else: 0}` prints its own source text.
   Recipe: hoist to `val x = if cond: 1 else: 0` and interpolate `{x}` —
   never an inline conditional inside `{}` on this lane.
6. **Enum `==` reads false for every variant** —
   [native_enum_eq_always_false_freestanding_2026-07-19.md](../../../../doc/08_tracking/bug/native_enum_eq_always_false_freestanding_2026-07-19.md).
   `config.execution_policy == FontExecutionPolicy.Suggested` is false even
   against a freshly constructed `Suggested` value — silently no-ops the
   whole vector-text pipeline (zero exceptions, zero pixels; hardest class
   to notice). Recipe: route around the comparison entirely — pin a known-
   good branch (`execution_target: "cpu"`) instead of trusting the enum
   compare. **Status: this specific pin in `engine2d_default_font_config_for`
   (engine.spl) is IN FLIGHT, not yet landed** — do not cite it as shipped
   until confirmed on origin.

Shares a signature with the general BoxInt `<<3` tag-shift family
(2026-07-04 seed ANY-channel enum-handle mangling) — same "tagged value
read at the wrong shift" shape, different call sites.

## Gotchas

- A fix that works hosted (interpreter/JIT) says nothing about the
  freestanding native lane — all 6 recipes above are freestanding-only.
  Re-probe via serial / gated `_probe_debug()` output after any change to
  this pipeline that must run on SimpleOS baremetal.
- Two miscompiled reads can cancel and look correct — verify a fix by
  disassembly or a fresh probe value, not by "the number looks right now."
- Per repo rule: a boring/compact construct that silently fails on this
  lane must be fixed or filed, not silently worked around without a doc.

## Update Rule

After any rasterizer, font-config, or Engine2D-text-path change —
especially anything touching the freestanding native-build lane — refresh
this skill with new landmine classes, recipe corrections, and landed/
in-flight status.

Template: `.spipe/spipe/doc/00_llm_process/template/feature_skill.md`
