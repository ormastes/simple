# Inline Item LayoutUnit Ceil & Pen Precision (Chrome 159)

> Traceability: `REQ-WEB-003` — Exact font-unit pen sums in `_text_pen_milli`, uniform `1/64` px `LayoutUnit` ceil in `layout_unit_ceil_milli`, and unified lead+item ceiling in `inline_item_width_err_milli_with_lead`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

## Scenarios

- **AC-1**: `e` of `renderable` after `<code>a</code>` takes Chrome 159's exact LCD quarter phase at pixels `(151,72)`, `(152,72)`, and `(157,72)` within `+-8` per channel without `@tag:in-development`.
