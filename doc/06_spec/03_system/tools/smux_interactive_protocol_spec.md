# Explicit-target interactive production API

**TEST_BLOCKED — authored manual; compilation, execution and docgen pending.**

Executable: `test/03_system/tools/smux_interactive_protocol_spec.spl`.
Requirements: `REQ-SMUX-INTERACTIVE-004`, `REQ-SMUX-INTERACTIVE-002`,
`REQ-SMUX-INTERACTIVE-003`.
Design: `doc/05_design/smux_interactive_protocol.md`.

These five scenarios call the actual service APIs and protocol dispatcher.
They create ordinary production sessions/windows without children; live input
delivery is deliberately asserted in the separate Windows scenario. No row is
an execution PASS.

| Scenario | Required production behavior | Status |
|---|---|---|
| Coherent frame capture | Valid explicit frame header; one service capture increment per API call | TEST_BLOCKED |
| Foreign ownership rejection | Wrong session/window/pane refused before capture metrics or I/O | TEST_BLOCKED |
| Independent view selection | Listing, layout and frame on second window leave global focus unchanged | TEST_BLOCKED |
| Input/history/layout/split refusal | Reject absent child, malformed UTF-8, invalid bounds/direction; retain pane count | TEST_BLOCKED |
| Reattach preserves layout | `current` retains known named plan, choosing tiled only for initial manual window | TEST_BLOCKED |

Require positive executed assertion counts from a qualified rebuilt runner and
regenerate this manual with docgen. Independent terminal processes, console
restoration and live child I/O require their own native system evidence.
