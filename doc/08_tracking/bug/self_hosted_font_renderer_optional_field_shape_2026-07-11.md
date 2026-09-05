# Self-hosted semantic resolver drops `FontRenderer.ttf_rasterizer`

Date: 2026-07-11
Status: Open
Severity: P1 — blocks Simple 2D vector-font integration

## Reproducer

```text
bin/simple test test/03_system/app/simple_2d/feature/simple_2d_vector_fonts_spec.spl --mode=interpreter
semantic: class `FontRenderer` has no field named `ttf_rasterizer`
```

The field is declared in `src/lib/nogc_sync_mut/text_layout/font_renderer.spl` as `ttf_rasterizer: FontRasterizer?`; constructors and existing methods reference it. The same field existed before this lane and the focused suite previously reached runtime loading, so this is a resolved-class-shape regression triggered by the extended owner/cache shape rather than a missing declaration.

## Attempts (bounded)

1. Expanded compact assignment syntax after the parser rejected assignment-bodied one-line forms.
2. Put every constructor named field on its own line.
3. Restored the optional custom-class field as the final class field.

All three post-fix executions still report the identical missing-field semantic error. Logs:

- `build/simple-2d-vector-fonts/system_spec_postfix.log`
- `build/simple-2d-vector-fonts/system_spec_postfix_2.log`
- `build/simple-2d-vector-fonts/system_spec_postfix_3.log`

## Required Next Investigation

Reduce the class/import cycle (`font_renderer` <-> `font_rasterizer`) against the self-hosted class-shape builder and compare the resolved field table before/after adding `FontCacheStats`/generation fields. Fix the owner semantic path once; do not replace the typed optional field with raw handles, module globals, or a feature-local runtime alias.
# 2026-07-11 follow-up

The import-cycle/class-shape failure is resolved by extracting shared types to
`font_types.spl` and lazily constructing the Engine2D renderer. Both native and
interpreter compilation now reach the scenarios.

The remaining blocker is runtime state propagation: `Engine2D.load_font()`
returns true, and the freshly rebuilt `libspl_fonts.so` directly reports a valid
face, `has_glyph('A') == 1`, and three positioned glyphs for `"A A"`. However,
the public Engine2D path still produces zero pixels and zero cache hits; bitmap
rendering after `unload_font()` is also suppressed in this system-spec process.
This strongly points at the module-global optional `FontRenderer` value being
copied or not retaining mutation across `_engine2d_fonts()` returns, rather than
a font parser or ABI failure.

The native scenario consumed the mandatory three verify/fix cycles. Continue in
a fresh scoped session with a reference-stable owner (for example an Engine2D
field or a boxed/shared renderer) and a one-assert state-retention probe before
re-running the full system spec.
