# Web renderer: negative left/top/order lose their sign; flex-basis-only item fills the row

Found 2026-11-14 by the combination matrix
(`sh scripts/check/check-web-combo-matrix-chrome.shs`, Chrome 159.0.8154.6).
Status: both FIXED in the same change; 21 matrix cells (56 element ids) left
the ratchet baseline.

## 1. `left` / `top` / `order` read with an unsigned parser

`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_decl_apply.spl`
read `left`, `top` and `order` with `parse_int`, which skips every non-digit
before the first digit, the minus sign included.

| declaration | Chrome x,y | Simple before |
|---|---|---|
| `position:relative;top:-5px;left:-5px` | -5,-5 | 5,5 |
| `position:absolute;top:-5px;left:-5px` | -5,-5 | 5,5 |
| flex row, middle item `order:-1` | middle x=0 | middle x=100 (sorted as `order:1`) |

Fix: `_decl_signed_int_or_zero` (same file) for those three properties.
Specs: `test/01_unit/browser_engine/negative_offset_and_order_spec.spl`
(reproduction: the three rows above; generalization: multi-digit negatives,
explicit `+`, unchanged positives, mixed orders -2/-1/0/1). Red (5 of 8 failing) -> green (8 of 8 passing).

Not fixed, same family: a negative `right` / `bottom`. The layout reads
`right_px >= 0` as "right is set", so the sign cannot be kept without a
separate is-set flag. Chrome: `position:absolute;right:-10px;bottom:-6px` in a
300x80 box is at x=293,y=62 (17x24); Simple puts it at 273,50.

## 2. `flex-basis` without `width` and without `flex-grow`

`simple_web_html_layout_renderer_layout_engine.spl`, row-flex placement: the
`width_px == 0` branch came before the `flex_basis_px > 0` branch. The measuring
pass had counted the item as a definite basis, so no auto weight existed and
the item kept the whole remaining inner width.

| row (300 px) | Chrome | Simple before |
|---|---|---|
| `aa`, `flex-basis:100px`, `bb` | w=100, `bb` at x=118 | w=282, `bb` at x=300 |

Fix: a basis-only branch ahead of the auto-width one.
Specs: `test/01_unit/browser_engine/flex_basis_without_grow_spec.spl`
(reproduction: the row above; generalization: two basis items, basis item as
first child). Red (4 of 4 failing) -> green (4 of 4 passing).

Not fixed, same family: `flex-basis:100px;flex-grow:1` (Chrome 264 px in that
row, Simple 282 px) and `flex-grow:1` on an item with a definite `width`
(Chrome 200 px, Simple 50 px; 17 matrix cells). Both need free space to be
distributed over items with a definite base, which the row pass does not do.
