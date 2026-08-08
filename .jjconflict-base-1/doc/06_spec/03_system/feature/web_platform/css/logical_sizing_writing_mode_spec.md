# CSS Logical Sizing And Writing Mode

> Mirrored manual for
> `test/03_system/feature/web_platform/css/logical_sizing_writing_mode_spec.spl`.

| Tests | Active | Skipped | Pending |
|-------|-------:|--------:|--------:|
| 2 | 2 | 0 | 0 |

| Manual status | Value |
|-------|-------|
| Source SHA-256 | `12c85ef23f151d899505e92622dc37cb21bdb41f82018c2847f9f80dd2d0330a` |
| Docgen | Pending — no admitted pure-Simple runner provenance is available |
| Runtime result | Not executed |

## Scope

This bounded scenario covers nonnegative integer-pixel `inline-size`,
`block-size`, their min/max longhands, and authored-order conflicts with
physical width/height for horizontal, vertical, and sideways writing modes.
It also covers inherited, stylesheet-normal, inline-normal,
stylesheet-important, and inline-important writing-mode winners.
It does not claim vertical text shaping or full CSS Writing Modes conformance.

## Requirement traceability

- `REQ-WEB-BROWSER-003`: resolves logical dimensions on the writing-mode axis.
- `REQ-WEB-BROWSER-004`: carries exact geometry through canonical Draw IR and
  renders discriminating pixels through the shared Engine2D compositor.
- `REQ-WEB-BROWSER-021`: supplies a modern executable SSpec and this mirror.

## Scenario

### should map logical sizes through writing mode into exact pixels

1. **Keep horizontal logical dimensions on width and height**
   - `inline-size:12px; block-size:20px` produces a 12 by 20 content rect.
   - Draw IR source kind remains `html_ast`.
2. **Swap vertical inline and block dimensions before layout**
   - The same sizes under `vertical-rl` produce a 20 by 12 content rect.
3. **Map vertical and sideways logical min and max constraints**
   - Sideways min/max fields map to physical width `[18,22]` and height
     `[10,14]`; minimum geometry is 18 by 10.
   - A later `min-inline-size:10px` clears the earlier `min-height:100vh`
     viewport flag on their shared vertical physical axis.
   - Vertical max constraints reduce 30 by 24 to 22 by 14.
4. **Preserve authored order between logical and physical axes**
   - A later vertical `block-size` beats width, while a later height beats
     `inline-size`, producing 20 by 9.
5. **Use the final inherited inline and important writing mode**
   - An inherited vertical mode overridden by inline normal resolves to
     horizontal 12 by 20.
   - Stylesheet-important vertical beats inline-normal horizontal and resolves
     to 20 by 12.
   - Inline-important horizontal beats stylesheet-normal vertical and resolves
     to 12 by 20.
6. **Render discriminating horizontal and vertical Engine2D pixels**
   - Neither composition skips a command.
   - Pixel `(19,11)` is white horizontally and blue vertically.
   - Pixel `(11,19)` is blue horizontally and white vertically.

### should preserve empty cell winners while pre-resolving writing mode

1. **Let stylesheet-important hide beat inline-normal show**
   - The empty cell is transparent and pixel `(5,4)` retains the blue table
     background.
2. **Let inline-important show beat stylesheet-important hide**
   - The same pixel is the cell's red background.

## Canonical route

The HTML producer resolves declarations in the existing Web style owner,
layout produces the shared `DrawIrComposition`, and the existing software
Engine2D compositor consumes that composition. No private WebIR, layout,
paint, cache, or font path is introduced.

## Evidence boundary

This is a complete handwritten scenario mirror pending qualified
`simple spipe-docgen`. Source inspection proves the prior implementation
always mapped inline size to width and block size to height. A provenance-bound
pure-Simple execution is still required before recording runtime PASS.

## Complete executable scenario reproduction

The complete runnable modern SSpec, including every setup helper, visible
`step("...")`, exact Draw IR assertion, and Engine2D pixel assertion, is:

`test/03_system/feature/web_platform/css/logical_sizing_writing_mode_spec.spl`
