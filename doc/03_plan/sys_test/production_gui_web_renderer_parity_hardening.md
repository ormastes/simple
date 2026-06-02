# Production GUI Web Renderer Parity Hardening System Test Plan

## Focused Command

Run the executable SPipe spec directly:

```bash
bin/simple test/system/wm_compare/production_gui_web_renderer_parity_hardening_spec.spl
```

Expected result: `4 examples, 0 failures`.

The current `bin/simple test <spec>` wrapper exits early before running this
spec in this checkout, so direct source execution is the recorded focused
evidence for this slice.

## Assertions

- Generated HTML contains `widget-button`, `widget-image`, and the expected
  `data-action` from the real GUI button.
- Generated HTML does not contain legacy fixture markers.
- Software pixels fill the requested viewport and contain more than three
  distinct colors.
- CPU SIMD pixels match software exactly.
- Metal pixels match software exactly; on macOS the backend must resolve to
  `metal`, otherwise it may resolve to `software`.
- `tolerance_used` is false.
