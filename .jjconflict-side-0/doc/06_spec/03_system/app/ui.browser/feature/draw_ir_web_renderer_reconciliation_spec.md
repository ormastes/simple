# Production Web composition submission

Run `release/x86_64-unknown-linux-gnu/simple test test/03_system/app/ui.browser/feature/draw_ir_web_renderer_reconciliation_spec.spl --mode=interpreter`.

Step: `Submit the production Web composition`.

## Executable setup and helper visibility

`setup_draw_ir_web_fixture` builds the production Web composition fixture and
its retained browser backend owner. `expect_composition_submission` checks the
composition submission receipt, including the Engine2D generation and rendered
rectangle. The scenario exposes both helper boundaries around the frozen step
rather than hiding setup or receipt checks in an unlabelled test body.

The scenario submits the same supplied `DrawIrComposition` twice, verifies one
retained Engine2D generation and initialization, verifies the supplied rect
reaches the framebuffer, then verifies one idempotent final shutdown. The
composition path records no HTML render or pixel-artifact work and reports its
CPU mirror as a completed readback. A resize is an explicit retained-owner
replacement boundary: it shuts down the old Engine2D before constructing the
new viewport-sized owner.
