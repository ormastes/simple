# Production GUI Web Renderer Parity Hardening Spec Manual

## Scenario

Validate the first production GUI/Web renderer parity slice for marker-free
generated widget HTML.

## Steps

1. Build GUI HTML using `common.ui.builder` and `render_html_tree`.
2. Confirm the HTML contains a real widget button, widget image, and button
   action.
3. Confirm the HTML does not contain legacy exact fixture markers.
4. Render the HTML at `96x72` through Simple Web Renderer software backend.
5. Render the same HTML through CPU SIMD backend.
6. Render the same HTML through Metal backend.
7. Compare CPU SIMD pixels against software with exact pixel comparison.
8. Compare Metal pixels against software with exact pixel comparison.
9. Fail if any tolerance is used, any mismatch is present, or the framebuffer is
   empty/monochrome.

## Evidence Command

```bash
bin/simple test/system/wm_compare/production_gui_web_renderer_parity_hardening_spec.spl
```

Expected focused result: `4 examples, 0 failures`.

## Notes

The CLI documented `spipe-docgen` command is not present in this checkout, and
`bin/simple test <spec> --format doc` exits before executing the spec. This
manual is therefore maintained directly until the doc generator is available.
