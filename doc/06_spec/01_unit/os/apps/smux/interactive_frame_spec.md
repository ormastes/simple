# Interactive input codec and VT frame projection

**TEST_BLOCKED — authored manual; compilation, execution and docgen pending.**

Executable: `test/01_unit/os/apps/smux/interactive_frame_spec.spl`.
Requirements: `REQ-SMUX-INTERACTIVE-002`, `REQ-SMUX-INTERACTIVE-004`.
Design: `doc/05_design/smux_interactive_protocol.md`.

All six scenarios use production codec, VT parser, pane records and snapshot
projection. Constructed state is the input to a pure renderer, not evidence of
native terminal/process execution. No scenario below is an execution PASS.

| Scenario | Required assertion | Status |
|---|---|---|
| Exact input decode | LF, ESC, NUL, Unicode scalars and single characters preserved without Enter | TEST_BLOCKED |
| Strict invalid input | Reject malformed hex, truncation, overlongs, surrogates, invalid continuations, non-scalars and >1024 bytes | TEST_BLOCKED |
| Styled actual VT | Render SGR, wide character continuation and positioned cursor; discard OSC title | TEST_BLOCKED |
| Synchronized output | Latched cells, styles and cursor shown until 2026 ends; then updated live frame | TEST_BLOCKED |
| Renderer boundary | Forged cell controls and style escapes cannot inject OSC | TEST_BLOCKED |
| Owner/byte limits | Reject foreign window/cursor pane and oversized serialized output | TEST_BLOCKED |

Run through the qualified rebuilt SSpec runner and preserve nonzero executed
scenario/assertion counts, then generate this manual with repository docgen.
Native ConPTY delivery remains the separate Windows system scenario's duty.
