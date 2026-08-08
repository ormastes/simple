# Web layout manager system evidence

Status: manual companion; executable source is `test/03_system/app/web_browser/feature/web_layout_manager_spec.spl`.

## Capture the CPU layout oracle

Render a grid and flex sibling through `simple_web_layout_render_html_draw_ir_result`. Adapt computed topology, typed box/flex/grid semantics, viewport and tracks while retaining `raw_boxes` only as oracle evidence; assert every structural id, arena index, and box coordinate.

## Classify browser layout islands

Locate the flex formatting boundary and build a layout-self frontier. Assert stable invalidated identity.

## Apply the invalidated frontier

Run the shared framework once in full mode and once incrementally. Require identical oracle boxes and fewer visited islands for the incremental run. Production retained frames use geometry fingerprints for the same frontier and skip manager execution for paint-only reuse.

## Verify fragments mappings and hit index

Require increasing epochs, generation-qualified hit regions, `LayoutOf` mappings, stale-generation rejection, unsupported-profile rejection, and epoch-exhaustion rejection.

Runtime execution remains held until an eligible canonical pure-Simple CLI restores `test`; the source contains no placeholder assertions.
