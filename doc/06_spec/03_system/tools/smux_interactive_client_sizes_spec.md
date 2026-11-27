# Interactive client dimension arbitration

**TEST_BLOCKED — authored manual; compilation, execution and docgen pending.**

Executable: `test/03_system/tools/smux_interactive_client_sizes_spec.spl`.
Requirement: `REQ-SMUX-INTERACTIVE-003`.
Design: `doc/05_design/smux_interactive_protocol.md`.

These three scenarios create real production session/attachment metadata and call
the actual interactive dispatcher. They do not substitute for two independently
rendered native terminal clients, and neither row is an execution PASS.

| Scenario | Required production behavior | Status |
|---|---|---|
| Different client dimensions | A 100x30 and a 40x12 attachment share a 40x12 canvas; a different session's 10x4 attachment has no effect; repeated frame requests preserve dimensions | TEST_BLOCKED |
| Resize and detach | Removing 40x12 expands to 100x30; updating remaining attachment reflows to 72x20; selected layout persists; foreign-session identity theft and invalid dimensions are refused | TEST_BLOCKED |
| Interleaved split and sibling frame | A vertical split on 20x6 retains the original pane at (0,0,9,6) and new pane at (10,0,10,6); two sibling frame requests preserve both IDs, all boundaries, pane sizes and manual layout while both clients remain attached | TEST_BLOCKED |

Preserve actual executed scenario/assertion counts and regenerate this manual
through docgen with the qualified rebuilt runner. Native acceptance additionally
requires two real clients of differing console sizes, live resize notification,
correctly clipped output and owner survival after either client detaches.

The source short-circuits unchanged canvas dimensions before applying a layout;
frame capture validates the persisted manual or named rectangle plan.
These scenarios do not instrument native resize calls; the general resize
metric does not count layout application and cannot prove their absence.
