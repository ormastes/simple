# Interpreter: `for` cannot iterate `List<T>` — "cannot iterate over this type"

Date: 2026-07-02
Status: fixed in source; direct interpreter execution pending a fresh pure-Simple runtime
Severity: P2
Found by: W6c lane agent (HUD-over-3D composition)

## Symptom

`error: semantic: cannot iterate over this type` for any `for e in list`
where `list: List<T>` in the self-hosted interpreter. `while + .get(i)`
works. Reproduced with a bare `for e in List<DisplayEntry>`.

## Impact

Breaks `surface_layer.composite_order` and
`compositor/stacking.spl::flatten_to_paint_order` (both `for`-iterate
Lists), i.e. the real 2D/3D LayerTree composition path. A stale seed-era
note in `test/01_unit/lib/engine/surface_layer_spec.spl` documents the
same limitation — still broken in the self-hosted binary.

## Related second bug (same lane)

`Scene3DLayer.attach(mut tree, ...)`: class params are pass-by-copy in
the interpreter even with `mut` — the `next_id` advance inside `attach`
is lost and subsequent `tree.create_layer` returns colliding layer ids
(both 0). A `mut` param on a class value silently mutates a copy.

## Workaround

`examples/11_advanced/game3d_hud/main.spl` uses LayerTree only for ids +
`z_paint_order`, and composites via a direct SoftwareBackend blit.

## Source fix (2026-07-15)

The interpreter now uses one iterable-array extractor for statement `for`,
`static_for`, and list comprehensions. Native arrays remain unchanged; a
canonical `List` is accepted only when its `items` field is an array. Text and
unsupported-value behavior, including existing diagnostics, are unchanged.
`src/compiler/10.frontend/core/interpreter/test_interp.spl` directly covers all
three List-backed forms.
