# Interpreter: `if val <name> = ...` local binding misresolved to a co-compiled global `fn <name>`

- Date: 2026-08-19
- Status: WORKED AROUND (rename at one site); interpreter defect OPEN
- Defect class: sibling of `compiler_cross_module_private_symbol_collision`,
  but for LOCAL pattern bindings vs global function symbols.

## Symptom

6 of 25 examples in
`test/02_integration/rendering/browser_session_script_css_animation_spec.spl`
failed with `semantic: type mismatch: cannot convert function to int` from
`keyframe_css_value` (`src/lib/gc_async_mut/gpu/browser_engine/style_block_parse.spl`).

## Root cause (bisected with a minimal probe)

```
if val rgba = parse_color_value_checked("#ef4444"):
    val masked = (rgba >> 24) & 255u32   # <- fails here
```

- Under a SMALL import set: passes.
- Under the full `browser_session_runtime.*` import set (which co-compiles
  `src/lib/gc_async_mut/gpu/engine2d/color.spl`, containing private
  `fn rgba(r,g,b,a) -> u32` at line 13): the identifier `rgba` inside the
  guarded block resolves to that FUNCTION, not the local Option payload, so
  `rgba >> 24` is function>>int.
- Renaming the local to `rgba_v` makes the identical probe pass.

## Workarounds landed

- `style_block_parse.spl` `keyframe_css_value`: local `rgba` -> `rgba_val`.

## Real fix needed

Locals (including `if val` pattern bindings) must always win name resolution
over co-compiled globals from other modules. This is the same resolution bug
family as the CSSValue enum collision
(`doc/08_tracking/bug/cross_module_cssvalue_enum_collision_2026-08-19.md`).
