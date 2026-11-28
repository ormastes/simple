# Float Paint Stacking Order (Chrome 159)

> Traceability: `REQ-WEB-001` — CSS 2.2 Appendix E float stacking order across Draw IR (`_html_draw_ir_node_paint_order`) and software raster (`_paint_passes`).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

## Scenarios

- **AC-1**: Non-positioned float (`float:right`) paints over overlapping later normal-flow block (`clear:left`) in Draw IR order, Engine2D (`k=1` / `k=4`), and software raster (`#332211` beats `#445566`).
- **AC-2**: Positioned sibling (`position:relative`) paints over non-positioned float and normal-flow blocks (`#cc2244` beats `#332211` and `#445566`).
- **AC-3**: Fractional-opacity non-positioned group containing a float retains contiguous Draw IR compositing and blended output.
