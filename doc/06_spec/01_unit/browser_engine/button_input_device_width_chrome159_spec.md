# Button & Input Device-Scale Width & Pen Precision (Chrome 159)

> Traceability: `REQ-WEB-003` — Gate unification across `plain_button_item`, `flex_row_button_label_at_edge`, and `button_in_flex_row_any`; exact label pen propagation for inline, `flex-wrap`, `row-reverse`, and `justify-content: center` buttons; device-shaped `<input type=button|submit|reset>` widths; `FORM_CONTROL_MEASURE_MAX_PX` enforcement at `k > 1`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

## Scenarios

- **AC-1**: Flex-row buttons with `flex: 1` or `min-width` keep matched layout and row device-width gates (`device-extra-width` omitted).
- **AC-2**: Auto-width buttons in inline, `flex-wrap: wrap`, `flex-direction: row-reverse`, and `justify-content: center` containers place label ink cleanly at `k=1` and `k=4`.
- **AC-3**: `<input type="submit" value="Forms &amp; Media">` matches `<button>` device-shaped width at `k=4`, and `200px` controls safely fall back via `FORM_CONTROL_MEASURE_MAX_PX`.
