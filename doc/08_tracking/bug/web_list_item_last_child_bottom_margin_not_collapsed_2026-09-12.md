# A list item is 16 px too tall: the last child's bottom margin does not collapse out

- Status: OPEN
- Area: `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl`
  (block auto-height accumulation)
- Found by: round-4 catalog geometry work against
  `test/fixtures/browser_engine/layout/round4_probe.html`

## Evidence (900 px, `16px/1.5 sans-serif`)

`<li><code>align-content</code> &mdash; partial<p>No claim.</p></li>`

| box | Chrome | Simple (after round 4) |
|---|---|---|
| `ul` h | 104 | **104** |
| `li` y | 120 | 120 |
| `li` h | 64 | **80** |
| nested `p` y | 160 | 160 |
| next `li` y | 200 | 200 |

Everything around it is now exact — the list block, the item's position, the
nested paragraph's position, and the following item. Only the item's own HEIGHT
is 16 px long, which is exactly the nested `<p>`'s UA `margin-bottom: 1em`.
CSS 2.1 §8.3.1: the bottom margin of an in-flow last child collapses THROUGH the
parent's bottom edge when the parent has no bottom padding or border, so it must
not be added to the parent's auto height. The renderer adds it.

Note the ordering evidence: because the following sibling `<li>` is at Chrome's
y=200, the margin is NOT being double-counted in the flow — the flow is right and
only the reported height is wrong, which narrows this to the height accumulator
rather than to margin collapsing in general.

This was masked before round 4 by a much larger error on the same box (the item
measured 128 px because of the byte/codepoint wrap defect,
`web_text_run_advance_measured_in_bytes_2026-09-12.md`).

## Round 5 (2026-09-12) — mechanism located exactly, NOT attempted, and why

The accumulator is `simple_web_html_layout_renderer_layout.spl:3216`:

```
    if child_count > 0:
        ...
        cy = cy + prev_margin_b
```

`prev_margin_b` is the LAST child's resolved bottom margin, and it is added into
the parent's own height unconditionally. CSS 2.1 §8.3.1 says that margin
collapses THROUGH the parent's bottom edge instead whenever the parent has
`padding-bottom: 0`, `border-bottom: 0`, an auto height, and does not establish
a new block formatting context — which is exactly `<li>`'s situation here. The
file already knows how to do this for the *self-collapsing* case (:3186-3200,
`self_collapsing` + `collapse_margins_signed`); the parent's own bottom edge is
the case it does not handle.

**Why round 5 did not change it.** Deleting the 16 px from `li1`'s height alone
would break two figures that round 4 made Chrome-exact: the margin has to
reappear in the PARENT's sibling gap, or `ul` drops 104 -> 88 and `li2` moves
200 -> 184. A correct fix therefore has to return the uncollapsed trailing margin
out of `layout_with_style` — a new field on `LayoutResult` (7 construction sites)
— and have every caller's accumulator do
`collapse_margins_signed(parent_own_margin_b, returned_trailing)` before placing
the next sibling. That changes the height of EVERY block whose last child has a
bottom margin, `body` included, so every one of the 8 catalog pages shifts and
the full pixel table must be re-measured. On this host one full pass of
`check-chrome-catalog-pixel-diff.shs` is ~1 h wall (8 pages, Chrome + an
interpreter-mode Simple render each), and round 5's budget was spent proving the
paint/layout advance parity fix. Landing half of this — the height change without
the sibling propagation — would regress two Chrome-exact figures to fix one, so
it was not started.

Unchanged and still true: `li`'s position, `ul`'s height and the next item's
position are all exact; only `li1`'s own height carries the 16.
