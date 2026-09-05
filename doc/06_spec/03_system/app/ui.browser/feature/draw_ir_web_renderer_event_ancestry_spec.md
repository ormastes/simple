# Draw IR Web renderer event ancestry

This operator scenario uses the public Panel2D interaction bridge, widget Draw
IR producer, and shared WM scene producer. It does not create a parallel hit
tree or infer a target from private geometry.

## Route canonical input

Step: `Route pointer and wheel through one ancestry`.

The `expect_event_ancestry` checker sends pointer-down and wheel input to the
same nested leaf, compares their canonical ancestor paths and semantic target
identity, and verifies that only the nearest nested scroll owner moves. It then
checks that the semantic widget target has a hit rectangle and that canonical
Web, widget, and WM Draw IR commands retain nonempty parent metadata and hit
rectangles. The Web document root is explicit (`document#root`), rather than
depending on a batch-level fallback.

Run with the admitted pure-Simple test runner and asserted BDD execution:

```text
bin/simple test test/03_system/app/ui.browser/feature/draw_ir_web_renderer_event_ancestry_spec.spl --mode=interpreter --assert-ran --fail-fast
```

Until that command passes through an admitted runner, this scenario is
source-ready evidence only and must not be reported as runtime PASS.
