# Cross-module CSSValue/CSSDeclaration enum collision breaks CSS-animation reconcile

- Date: 2026-08-19
- Status: WORKED AROUND (rename); compiler defect remains OPEN
- Defect class: `compiler_cross_module_private_symbol_collision` (same class the
  JIT already warns about for functions; this is the TYPE/enum variant flavor)

## Symptom

6 of 25 examples in
`test/02_integration/rendering/browser_session_script_css_animation_spec.spl`
failed with `semantic: type mismatch: cannot convert function to int`, thrown
from `keyframe_css_value` in
`src/lib/gc_async_mut/gpu/browser_engine/style_block_parse.spl` whenever the
whole-program compile also loads `src/lib/common/render_scene/css_types.spl`.

## Root cause (reproduced)

Two enums named `CSSValue` (and two `CSSDeclaration`) were co-compiled:

- `src/lib/gc_async_mut/gpu/browser_engine/style/animation.spl`:
  `Percentage(v)`, `Color(color: Color)`, `Number(v)`, ...
- `src/lib/common/render_scene/css_types.spl`:
  `Percent(v)`, `Color(c: Color)`, no `Number`.

Minimal repro (kept the failure shape exactly): a spec importing BOTH modules
and constructing `CSSValue.Percentage(v: 50.0)` from the animation enum fails
with `unknown variant or method 'Percentage' on enum CSSValue` — variant
resolution bound to the render_scene enum. `CSSValue.Color(color: ...)`
misbinds the same way and surfaces as "cannot convert function to int".

## Workaround landed

Renamed the render_scene types to `RsCssValue` / `RsCssDeclaration`
(`css_types.spl`, `src/app/ui.browser/renderer.spl`,
`src/app/ui.browser/dom_bridge.spl`) — they had almost no consumers.

## Real fix needed

Enum/type resolution must be module-scoped (or collisions must be a hard
compile error), like the existing function-collision warning but fatal.
