# Web tile paint-op allocation hardening

Status: allocation hardening implemented; performance classification pending.

`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_layout.spl` built the paint-op list with repeated bare `Array.push` calls across multiple node passes. The currently admitted runtime has evidence that *reassigned* `array = array.push(value)` can be quadratic, but does not yet prove the same for bare `array.push(value)`. The old implementation therefore had growth-strategy-dependent allocation pressure, not a measured quadratic defect.

The hardening preallocates the strict `3 * node_count` upper bound, writes by index, and performs one linear ordered-prefix finish. Owner: web renderer performance lane. Unblock: run `test/01_unit/lib/gc_async_mut/gpu/browser_engine/tile_op_buffer_linear_finish_spec.spl` and representative before/after 4K profiling through an admitted Stage-4 CLI; classify it as a performance fix only if those measurements establish the regression.
