# Web layout manager guide

Use `web_layout_adapt_cpu_oracle` on `SimpleWebLayoutDrawIrResult`, then build changes with `web_layout_change` and reduce them with `web_layout_dirty_frontier`. Construct one `WebLayoutManager` per DOM generation and carry the returned manager into the next full or incremental call.

Treat `raw_boxes` as authoritative. Do not use scroll-adjusted `hit_index.boxes`, infer containment from clipping, or pass an unsupported profile. A stale generation, unsupported profile, non-convergence, or exhausted epoch returns an explicit fault without advancing manager state.

The result retains the framework `LayoutSnapshot` and adds generation/epoch-qualified hit regions. Draw IR remains downstream.

