# Web decimal geometry provenance and scene admission

Manual companion to
`test/03_system/app/ui/feature/web_decimal_geometry_provenance_spec.spl`.
Generated SPipe output awaits a trustworthy Simple runner.

## Primary flow

1. Render bounded inline HTML through the real Web layout producer.
2. Inspect the matching hit-index node's authored geometry tokens and unresolved flag.
3. Inspect the matching source DrawIR command's `box-geometry-raw-tokens` and
   `box-geometry-unresolved` properties where the integer renderer emitted a command.
4. Ask `web_decimal_geometry_rejection_reason(html)` for the scene-level admission
   result before treating any command inventory as complete.

## Scenarios and expected evidence

| Scenario | Source evidence | Admission expectation |
|---|---|---|
| Direct decimal `left`, `top`, `width`, `height` in inline style, one at a time | Each authored token survives on the node and emitted command; unresolved is true | Nonempty rejection |
| Stylesheet class with only decimal `width` and `height` through fast dispatch; position and paint are separate inline declarations | Each token survives the class cascade on node and command; unresolved is true | Nonempty rejection |
| `0.5px` by `0.5px` subpixel box | Hit-index node and both tokens survive; the integer renderer emits no box command | Nonempty scene-level rejection |
| Integer `1px,2px,4px,3px` control | Exact source DrawIR bounds; unresolved is false | Empty reason |
| Decimal positioned ancestor with integer child | Ancestor retains `left=0.5px` and unresolved flag; child remains in node arena | Nonempty rejection |
| `min-width:calc(2px + .5px)` constraint | Authored constraint token and unresolved flag survive | Nonempty rejection |
| Positioned box with `clip:rect(0.5px, 4px, 4px, 0px)` | Authored legacy clip token and unresolved flag survive before integer clip parsing | Nonempty rejection |

This is a rejection-only contract. It proves neither fractional rasterization nor a
physical GPU capture. The spec must execute before claiming PASS.

Requirements: REQ-2D-002, REQ-2D-006.
