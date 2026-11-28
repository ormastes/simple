# Auto-width Button & Input-Button Boxes at Device Scale (Chrome 159)

> Traceability: `REQ-WEB-003` — button / input-button label width and pen match Chrome 159 at k = 1 and 4 (border columns and label ink measured in Chrome 159 headless screenshots).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

## Scenarios

- **AC-1**: A 200 px button label keeps its exact width at k = 1 and 4 (the `FORM_CONTROL_MEASURE_MAX_PX` fallback): right border at 276 / 1103 device px.
- **AC-2**: What follows an `<input type=submit|button|reset>` starts at the input's LayoutUnit width, and the following button's right edge is round(k x exact right).
- **AC-3**: Inline, wrapped, reversed and centred button rows keep Chrome's border columns and label ink at k = 1 and 4.
- **AC-4**: Text after a button, or after a chain of buttons, keeps Chrome's columns at k = 1 and 4.
- **AC-5**: At k = 4 the text after `Exercise controls` starts at the button's device-shaped LayoutUnit width; its glyph dark-run starts match Chrome on device rows 53, 57, 60, 64.
