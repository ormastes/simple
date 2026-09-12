# Auto-width flex items fill a whole line in a wrapping row (2026-09-12)

**Status:** FIXED (this change).
**Component:** pure-Simple web renderer, row-flex layout, `flex-wrap` branch.
**File:** `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl`
(`base_w_wrap`, in both the wrap MEASUREMENT loop and the wrap PLACEMENT loop).

## Symptom

In a `display: flex; flex-wrap: wrap` container, every child with `width: auto`
and no `flex-basis` was given the container's full inner width, so each child
wrapped onto a line of its own. Chrome puts them side by side.

## Evidence

Chrome, `examples/06_io/ui/web_catalog/overview.html` at 900x760:

```
div.flex  top=271.78 h=80.00  w=810.00
ol        top=287.78 h=48.00  w=133.38
ul        top=287.78 h=48.00  w=150.28    <- SAME top as the ol
```

Simple, same page, layout-box dump:

```
div  y=271 h=124 w=810
ol   y=287 h=48  w=810      <- full container width
ul   y=355 h=48  w=810      <- pushed onto a second line
```

`124 - 80 = 44` — this single container accounts for the overview card ending at
y=414 instead of Chrome's 371 (the +43 recorded in
`doc/08_tracking/bug/web_block_vertical_advance_12pct_2026-09-12.md`, rank 4).

The same shape dominates `css-layout.html`, the worst page (29.19 % mismatch).
An element-by-element diff of the two geometry dumps shows the first structural
divergence at the page's wrapping flex row: Chrome lays three items out at
`w=262` on one line at `y=169`; Simple lays them at `w=810` on three lines at
`y=145/205/265`. Every later element on the page inherits that 120 px of drift.

## Cause

```
val base_w_wrap = if cst.flex_basis_px > 0: cst.flex_basis_px
                  else: if cst.width_px > 0: ...
                  else: if cst.width_px < 0: iw else: iw
```

Both `width_px` branches collapse to `iw`. The NON-wrapping branch of the same
function already does the right thing — when a child has no basis and no width
it calls `intrinsic_text_width(...)` and, for `flex_grow == 0`, uses that
max-content width as the base size. Only the wrap branch was never given that
treatment, which is why buttons in the (non-wrapping) catalog tab strip are
shrink-to-fit while lists in the (wrapping) overview card are not.

## Fix

In the wrap branch, for an item with no `flex-basis`, `width_px == 0` and
`flex_grow == 0`, use `intrinsic_text_width` capped at `iw`, exactly as the
nowrap branch does. Items with a basis, an explicit width, a percentage width
(`width_px < 0`) or a non-zero `flex-grow` are untouched — a growing item still
starts from the container width and is distributed as before.

The measurement loop and the placement loop compute `base_w_wrap` separately and
BOTH are changed; changing only one makes the measured line breaks disagree with
the placed widths.

## Spec

`test/01_unit/browser_engine/flex_wrap_auto_width_item_spec.spl` — absolute
Chrome oracles: the two lists share one `y`, the container is `h == 80`, and
neither list is stretched to the container width.
