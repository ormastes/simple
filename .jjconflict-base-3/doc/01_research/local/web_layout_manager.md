# Web layout manager local research

The canonical oracle is `SimpleWebLayoutDrawIrResult.raw_boxes`; its arena arrays preserve unscrolled geometry. `hit_index.boxes` is scroll-adjusted and must not seed layout. `base_styles`, `hit_index.nodes`, and `hit_index.child_index` provide the computed-style and DOM projections.

The structural framework already owns island discovery, dependency waves, fixed-point bounds, backend selection, `LayoutOf` mappings, and receipts. The browser manager must adapt inputs and invalidation only; a second scheduler or geometry cache would duplicate authority.

Browser arena index `i` maps to structural id `i + 1`; id `0` remains the framework sentinel. Current style data can classify block, inline, flex, grid, table, absolute/sticky, scroll, and replaced contexts. Authored containment is not preserved, so the adapter must report it as false rather than infer it from overflow.

The existing renderer modules are large and shared. The first checkpoint therefore freezes consumer-owned contracts without changing renderer files.

