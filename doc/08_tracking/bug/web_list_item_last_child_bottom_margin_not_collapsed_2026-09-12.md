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
