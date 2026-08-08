# HTML address element rendering

> Static candidate manual — runtime unclaimed. This is the complete
> hand-reviewed mirror of the executable scenario, not generated PASS evidence.

Requirements: REQ-WEB-BROWSER-002, REQ-WEB-BROWSER-003,
REQ-WEB-BROWSER-004, REQ-WEB-BROWSER-021.

## Fixture profile

Every 80-by-20 fixture uses a white page and the text `iiiiWWWW`. The target
is 80-by-16 with background `#fef3c7`.

| Variant | Element and authored declaration | Expected style |
|---|---|---|
| selected | `<address>` with no override | block, italic |
| italic control | `<div style="font-style:italic">` | block, italic |
| dispatch override | `<address style="font-style:normal">` | block, normal |
| full override | `<address style="font-style:normal;visibility:visible">` | block, normal |
| normal control | `<div style="font-style:normal">` | block, normal |

## Parse address as a semantic body child

The parser/tree result retains `body#body > address#target`; the target tag is
exactly `address`.

## Resolve address UA typography through both style paths

The selected target has `display == "block"` and
`font_style_italic == true`. The standalone override selects direct dispatch;
the visibility-bearing override selects full Style reconstruction. Both expose
`font_style_italic == false`.

Selected, dispatch, and full target geometry is exactly `[0,0,80,16]`.

## Emit absolute address Draw IR geometry

The canonical target command is a `rect` at `[0,0,80,16]` with color
`0xFFFEF3C7`, `tag=address`, and `display=block`. Selected box/text commands
carry `font-style=italic`; both authored override box/text commands carry
`font-style=normal`. Every text command starts at absolute origin `[0,0]`.

No private font renderer, parallel WebIR, Draw IR command, or Engine2D path is
introduced.

## Rasterize address typography with exact pixel controls

Each Engine2D frame is 80-by-20 and skips zero commands.

- Absolute pixel `(79,15)` is `0xFFFEF3C7`.
- Absolute pixel `(1,18)` is `0xFFFFFFFF`.
- The selected `<address>` frame is pixel-identical to the explicit italic
  `div` control.
- The direct and full override frames are each pixel-identical to the explicit
  normal `div` control.
- The selected and direct-override frames differ at one or more pixels, proving
  that italic presentation reaches Engine2D rather than remaining metadata.

## Claim boundary and provenance

This slice claims selected medium-UA block/italic address presentation and
standalone normal override parity. It does not close the grouped HTML Partial
backlog. No runner, bootstrap, or docgen was invoked; all values remain static
expected oracles pending qualified pure-Simple execution.
