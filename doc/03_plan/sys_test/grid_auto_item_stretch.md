# CSS Grid auto-size item stretch system-test plan

## Scope

Prove the bounded CSS Grid rule that a non-replaced item with an automatic
block size uses the full size of one explicit pixel row when effective
`align-self`/`align-items` is `normal` or `stretch` and neither physical
block-axis margin is automatic.

The production path remains:

`HTML/CSS -> computed Style -> shared layout -> DrawIrComposition -> Engine2D`

No parser, Web IR, Draw IR schema, painter, backend, runtime, or compiler change
is part of this lane.

## Executable specification

- `test/03_system/feature/web_platform/css/grid_auto_item_stretch_spec.spl`
- Hand-reviewed static manual (not generated-runtime evidence):
  `doc/06_spec/03_system/feature/web_platform/css/grid_auto_item_stretch_spec.md`
- Requirements: REQ-WEB-BROWSER-003, REQ-WEB-BROWSER-004, and
  REQ-WEB-BROWSER-021.

## Frozen scenario flow

1. `Parse the styled HTML fixture`
2. `Resolve semantic layout and computed style`
3. `Emit canonical Draw IR`
4. `Render exact Engine2D pixels`

## Exact acceptance oracles

- Primary layout: Grid `[0,0,8,4]`, red `[0,0,4,4]`, blue `[4,0,4,4]`.
- Primary Draw IR: stable `grid`, `red`, and `blue` rectangle commands; full
  `[0,0,8,4]` clip; exact `0xFFDC2626` and `0xFF2563EB` colors.
- Engine2D: zero skipped commands and a literal 32-pixel buffer containing four
  identical red-red-red-red/blue-blue-blue-blue rows.
- Negative controls: `align-self:start` stays 1px high; a block-axis auto margin
  stays 1px high; authored `2px` and `0px` heights remain authoritative.
- Split-cascade metadata: stylesheet `height:0px` and authored alignment
  survive a later unrelated inline `visibility` declaration through the
  non-dispatch full Style reconstruction path.
- Logical sizing: the final cross-phase writing mode maps vertical
  `inline-size:0px` and horizontal `block-size:0px` to physical height while
  keeping `height_px == 0` and `height_auto == false` in agreement.
- Box-model control: an 8px row with 1px top/bottom margins, padding, and borders
  resolves to border box `[12,1,4,6]`.
- Single-track boundary: a two-column span remains `[0,8,8,1]`.
- Single-track boundary: a two-row span remains `[16,8,4,1]`.
- Replaced-element boundary: an explicitly stretched `video` remains
  `[8,8,4,1]`.
- Alignment semantics: an aspect-ratio-derived non-replaced item stays 2px high
  under `normal` but reaches 4px under explicit `stretch` while its authored
  height is auto.
- Omitted alignment: the legacy stored `stretch` default is identified as
  unauthored and follows Grid initial `normal` behavior for an aspect-ratio
  item.
- Nested control: `align-items:normal` stretches an automatic-height nested Grid
  to `[0,0,4,4]` while retaining its `2px 2px` columns and 4px row.

## Explicit exclusions

Stretching spans, implicit-row stretch, intrinsic/flexible tracks, replaced
elements, auto-margin distribution, non-start self-alignment positioning, and
full CSS Grid/WPT parity remain separate work.

## Verification budget

This correction cycle is static-only. Do not run a runtime, bootstrap, or
docgen. The earlier seed-backed invocation is diagnostic only and is not a
qualified PASS. Keep the manual hand-reviewed and label its values as expected
oracles until a retained pure-Simple runner execution can replace that status.
