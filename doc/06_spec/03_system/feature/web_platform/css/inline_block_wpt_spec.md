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
contribution through semantic, Draw IR, and absolute pixel evidence. Remaining
advanced inline-block baseline alignment stays in the compatibility ledger.

## Align empty baseline inline-block bottom edges through canonical Draw IR

The scenario uses two empty inline-blocks with zero margin, padding, and
border, at heights 8px and 20px. Both compute `vertical-align:baseline`.

1. **Render HTML and CSS through canonical Draw IR**
   - Keeps this evidence on the frozen production Draw IR step.
2. **Resolve baseline alignment in computed Style**
   - Both values must be `baseline`.
3. **Lay out empty atomic inline-blocks on their shared baseline**
   - The 8px box is at `y=12`; the 20px box is at `y=0`.
   - Both bottom edges establish the baseline at `y=20`.
   - The default 18px parent strut applies 1px half-leading around the 16px
     font: its baseline offset is 15px and descent is 3px, so the following
     block starts at `y=23`.
4. **Preserve baseline geometry in canonical Draw IR before pixels**
   - Draw IR carries the same positions and baseline bottom edges at `y=20`.
   - It separately places the following block at the full line-box bottom,
     `y=23`.

This is deliberately the empty-inline-block pixel-margin baseline slice.
Non-empty and overflow inline-block baselines plus negative/percentage vertical
margins remain unsupported in the compatibility ledger.

## Include the parent strut, text, and margins in an empty inline-block baseline line

The control scenario uses a 16px parent font with a 12px line-height, visible
inline text, and empty baseline inline-blocks with 2px/3px and 1px/4px vertical
margins. The taller block's bottom margin edge establishes the shared baseline
at 25px. Therefore the short border box is at `y=14`, the tall box at `y=1`,
the visible text at `y=13`: the 12px line-height has -2px half-leading, so its
baseline offset is 12px (`25 - 12 = 13`). The following block begins at `y=25`.

The evidence remains computed Style, canonical layout, then Draw IR; it does
not need pixels to establish this geometry contract.
