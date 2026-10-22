<!-- codex-design -->
# GUI rendering evidence view — proposed

Status: design only; broader comparison scope awaits feature and NFR selection.
This view consumes completed receipts. It does not select a renderer, perform
readback, or infer correctness from a screenshot alone.

```text
┌ Rendering case: 16-group-opacity ─────────────────────────────────────────┐
│ Input  HTML+asset hashes ✓   640×480 @1×   state: ready   fonts: checked  │
│ Routes  Chrome/ANGLE Vulkan  |  Simple/native Vulkan  |  Skia: unavailable │
│ Frame   Chrome #42 complete  |  Simple #42 complete  |  source revision ... │
├──────────────────────┬──────────────────────┬───────────────────────────┤
│ Reference pixels     │ Simple pixels        │ Difference                │
│ [full image]         │ [full image]         │ [full image]              │
├──────────────────────┴──────────────────────┴───────────────────────────┤
│ Verdict  FAIL_VISUAL   region: overlap   max Δ: 31   changed: 2,440 px     │
│ Source   group-opacity > card-stack   effect: isolated opacity 0.5         │
│ Evidence [receipt] [raw images] [RenderDoc diagnostic] [event log]         │
└─────────────────────────────────────────────────────────────────────────────┘
```

Required visible states: `PASS`, `FAIL_VISUAL`, `FAIL_SEMANTIC`,
`UNSUPPORTED_FEATURE`, `BLOCKED_ENVIRONMENT`, `CAPTURE_ERROR`, and
`INCOMPLETE_FRAME`. A blocked or incomplete state shows its reason and never a
green diff panel. The final-image verdict cites the resource selection, decoded
pixel domain, frame completion, input hashes, device/route and fixture rule.
Event counts, event order and thumbnail mismatch appear only in a diagnostic
drawer. An unimplemented Skia route displays `unavailable`, not a simulated image.

For GUI widget cases, show the widget tree ID, state, focus and delivered pointer
or keyboard events beside the same three image panes. A screenshot alone cannot
prove that input reached a visible control. Retain full-resolution source images
and diff under the scenario's evidence path; thumbnail previews are navigation.

System-spec captures should link the receipt and images from the mirrored
`doc/06_spec/` manual. Test setup and capture helpers must fail explicitly until
implemented; no static preview can satisfy a live-rendering acceptance test.
