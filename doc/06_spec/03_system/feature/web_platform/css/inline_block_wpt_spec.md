# CSS Inline-Block Formatting

Source: `test/03_system/feature/web_platform/css/inline_block_wpt_spec.spl`

## Keep inline-block border boxes in one atomic inline run

Requirement coverage: `REQ-WEB-BROWSER-002`, `REQ-WEB-BROWSER-003`.

The scenario uses the production HTML/CSS layout and Draw IR producer with an
80×48 viewport. Two adjacent `span` elements each declare a 20×12 content box,
2px padding, and 1px border.

1. **Resolve inline-block as the computed display value**
   - Both elements must retain `display:inline-block`.
2. **Lay out exact atomic border boxes on one line**
   - The first border box is `(0, 0, 26, 18)`.
   - The second border box is `(26, 0, 26, 18)`.
   - The following block starts at `y=18`.
3. **Lower the same absolute boxes through canonical Draw IR**
   - Draw IR must preserve the computed display value and both exact border
     boxes before any Engine2D pixel execution.

The focused contract covers atomic inline participation, explicit content-box
sizing, padding/border contribution, horizontal placement, and line-height
contribution. Advanced inline-block baseline alignment remains listed in the
compatibility ledger.
