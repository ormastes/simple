# `WebBoxShadow.none()` does not exist — legacy box-shadow parser stops on `none` / short layers (2026-11-14)

Status: OPEN. Severity: low (module has no importer inside `src/`).

## Defect

`src/lib/gc_async_mut/gpu/browser_engine/dom_visual_effects.spl:43` and `:61`
return `WebBoxShadow.none()`. `WebBoxShadow` is a plain struct
(`src/lib/gc_async_mut/gpu/browser_engine/css.spl:7`) with no `none`
constructor. The same struct declares `color: text` while the parser stores a
packed `u32`.

## Repro (seed built 2026-11-14, interpreter)

```
use std.gc_async_mut.gpu.browser_engine.dom_visual_effects.{parse_box_shadows}
fn main():
    print parse_box_shadows("none").len()
```

Expected: `0` (CSS `box-shadow: none` is an empty layer list).
Actual: `error: semantic: unknown static method none on class WebBoxShadow`.
The same happens for `""` and for any layer with fewer than three tokens.

## Scope

`parse_box_shadows` / `parse_single_box_shadow` have no caller outside this
file; the live path is `simple_web_css_box_effects.spl`. Either delete the
legacy parser or give the struct a `none()` constructor and a `u32` colour.

## Evidence

`test/01_unit/lib/gc_async_mut/gpu/browser_engine/css_box_shadow_and_supports_spec.spl`
covers the working inputs and deliberately omits the failing ones.
