# CSS Inline-Block Formatting

Source: `test/03_system/feature/web_platform/css/inline_block_wpt_spec.spl`

## Keep inline-block border boxes in one atomic inline run

Requirement coverage: `REQ-WEB-BROWSER-002`, `REQ-WEB-BROWSER-003`.

The scenario uses the production HTML/CSS layout, Draw IR producer, and
BrowserRenderer Engine2D pixel readback with an 80×48 viewport. Two adjacent
`span` elements each declare a 20×12 content box, 2px padding, and 1px border.

1. **Resolve inline-block as the computed display value**
   - Both elements must retain `display:inline-block`.
2. **Lay out exact atomic border boxes on one line**
   - The first border box is `(0, 0, 26, 18)`.
   - The second border box is `(26, 0, 26, 18)`.
   - The following block starts at `y=18`.
3. **Lower the same absolute boxes through canonical Draw IR**
   - Draw IR must preserve the computed display value and both exact border
     boxes before any Engine2D pixel execution.
4. **Read exact interior and control pixels through Engine2D**
   - Known interior pixels must be red in the first box and blue in the second.
   - A pixel to the right of both boxes must retain the white page background.
   - A pixel where the second box would appear if wrapped must remain white.

The focused contract covers atomic inline participation, explicit content-box
sizing, padding/border contribution, horizontal placement, and line-height
contribution through semantic, Draw IR, and absolute pixel evidence. Advanced
inline-block baseline alignment remains listed in the compatibility ledger.
