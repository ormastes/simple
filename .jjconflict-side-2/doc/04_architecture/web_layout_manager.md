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
 boxes/fragments/lines/overflow + mappings + receipt + epoch
```

`WebLayoutSnapshotAdapter` owns browser-to-structural identity and profile classification. Structural id `i + 1` is paired with the generation-qualified DOM route id; neither is substituted for the other. `WebLayoutManager` owns only generation/epoch admission and delegates scheduling.

Snapshots carry family-aware text requests and already-resolved per-node font identity, advances, width, and line height from the CPU oracle. The manager supplies those exact results through `TextMeasurePort`; it does not invent a page-wide font family, approximate shaping, or infer containment from `overflow_hidden`.

The CPU renderer remains the geometry oracle. Draw IR remains downstream and receives no transient text atlas state. GPU policy is only a candidate: a consumer execution port must prove submission, synchronization, device readback, and oracle equality before a GPU receipt is valid. Hit regions add explicit `HitRegionOf` edges without changing structural identity.

The adapter lowers computed styles into typed `LayoutNodeSemantics`; it never packs `raw_boxes` into device input. The retained render session compares generation-qualified geometry fingerprints, calls full layout for rebuilds, incremental layout for exact dirty frontiers, and does not advance layout epoch for paint-only reuse. The CUDA consumer currently admits fixed childless block/flex/grid roots and pre-rejects wider browser semantics.

`SimpleWebRenderSession` is the production integration owner. After the CPU result is complete, it adapts that result, runs the generation-matched manager, and retains the framework snapshot/result beside the visual result. Reused frames retain the prior manager result without advancing its epoch; close clears all retained layout state.
