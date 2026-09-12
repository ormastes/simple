# CSS min() / max() / clamp() were not parsed on lengths (2026-09-12)

**Status:** FIXED for `width`.
**Component:** pure-Simple web renderer, declaration application.

## Defect

No CSS math function parser existed anywhere in `browser_engine/`. A
`width: min(1100px, 100%)` declaration fell through to `parse_int()`, which read
the first number it found, so the box was sized 1100px and overflowed its
containing block. Measured on the catalog: the overview card spanned x=25..**899**
vs Chrome's 25..874; isolated at 300x200, `width:min(1100px,100%)` gave
24..**299** while `width:auto` and `width:100%` both correctly gave 24..275.

## Fix

The width model stores ONE i32 per box (positive = px, negative = percent
sentinel resolved at layout time), so a mixed `min(1100px, 100%)` cannot be
represented directly. It is desugared instead, which is exactly equivalent under
CSS sizing and reuses the `min_width_px` / `max_width_px` slots that already
existed and are already applied after percentage resolution
(`..._layout.spl:779-790`, `constrained_outer_width`):

```
width: min(Apx, B%)        ==  width: B%;   max-width: Apx
width: max(Apx, B%)        ==  width: B%;   min-width: Apx
width: clamp(lo, mid, hi)  ==  width: mid;  min-width: lo; max-width: hi
```

All-px and all-percent argument lists fold directly. The implied clamp only
fills a slot the author left unset.

New helpers `css_math_primary`, `css_math_implied_min_px`,
`css_math_implied_max_px`, `css_math_args` at the end of
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_style.spl`
(that module is `export use`d by both declaration appliers). Wired at BOTH width
sites — the dispatch fast path
(`..._declarations.spl`, `CSS_PROP_WIDTH`) and the slow path
(`..._decl_apply.spl`) — because the fast path short-circuits the slow one for
simple declaration blocks.

## Specs

`test/unit/browser_engine/css_math_length_spec.spl` (mirrored into
`test/01_unit/browser_engine/`), 11 examples:

- **Reproducing** — `describe "CSS math lengths resolve against the containing
  block"`: `min(1100px,100%)` resolves to 852 in an 852px viewport and to 1100 in
  a 1400px one; `clamp(100px,50%,300px)` → 200 at 400px and 300 at 1000px;
  `max(400px,10%)` → 400 at 900px. The oracle is an absolute red-pixel run count
  on a fixed row, i.e. the resolved border-box width.
- **Generalization** — `describe "CSS math lengths resolve from a <style> rule
  too"` (the catalog's actual shape: the comma must survive the stylesheet
  declaration tokenizer) and `describe "CSS math desugaring — value level"`
  (direct unit tests of the three helpers, including all-px folding and
  pass-through of a plain length).

## Sabotage verification

Making `css_math_primary` return its input unchanged took the file from
`11 examples, 0 failures` to `5 failed`; removing the sabotage restored green.

## Not done

`height` / `min-*` / `max-*` / `gap` / `padding` still ignore CSS math functions —
only `width` is wired. Nested `calc()` inside `min()`/`clamp()` is NOT handled:
this declaration path uses bare `parse_int` and has no `calc` evaluator at all,
so "nest it in calc" was not applicable here. `css_math_args` already tracks
paren depth, so a future `calc` evaluator drops in without re-tokenizing.
