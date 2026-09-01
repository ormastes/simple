# Web layout manager architecture

The browser layout capsule is a thin MDSOC consumer above `std.common.structural.layout`. The authoritative geometry source is `simple_web_layout_render_html_draw_ir_result(...).raw_boxes`, never the scroll-adjusted `hit_index.boxes`. Its aligned projections are `hit_index.nodes`, `hit_index.child_index`, `hit_index.styles`, and `base_styles`.

```text
renderer CPU oracle + DOM/style projection
                 |
       WebLayoutSnapshotAdapter
                 |
   WebLayoutChange -> dirty frontier
                 |
          WebLayoutManager
                 |
  layout_run_full / layout_run_incremental
                 |
 boxes + LayoutOf mappings + StageReceipt + epoch
```

`WebLayoutSnapshotAdapter` owns browser-to-structural identity and profile classification. Structural id `i + 1` is paired with the generation-qualified DOM route id; neither is substituted for the other. `WebLayoutManager` owns only generation/epoch admission and delegates scheduling.

Phase-one snapshots carry already-resolved per-node font identity, advances, width, and line height from the CPU oracle. They do not invent a page-wide font family or infer containment from `overflow_hidden`. Live text recomputation waits for a family-aware framework request contract.

The CPU renderer remains the geometry oracle. Draw IR remains downstream and receives no transient text atlas state. GPU work is a backend selected by the framework cost model, not a parallel browser layout path.
