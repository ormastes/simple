# Terminal client wire and viewport contracts

Authored review copy; execution, SPipe generation, zero-stub receipt and
maintenance scan remain **TEST_BLOCKED**. These ten pure scenarios do not
prove a working Windows console, transport or independent interactive clients.

Source: `test/01_unit/os/apps/smux/client_view_spec.spl`.

| Requirement | Scenario and observable result |
|---|---|
| INTERACTIVE-002 | Encode Ctrl-C, CR, arrows, spaces and Unicode as exact hex without adding a newline |
| INTERACTIVE-003 | Read ordered resource identities, cycle locally and refuse malformed/duplicate identities |
| INTERACTIVE-003 | Recover selection from a changed list and handle an empty list |
| INTERACTIVE-004 | Preserve all styled frame content after validating its dimension header |
| INTERACTIVE-004 | Refuse missing, malformed or oversized frame headers |
| INTERACTIVE-005 | Move a local history viewport without modifying saved rows |
| INTERACTIVE-005 | Clamp older/short/empty history safely |
| INTERACTIVE-005 | Clip old wider history by Unicode cells and filter control replay |
| INTERACTIVE-005 | Show the selected line range with a generated reverse-video style |

All shortened IDs use the `REQ-SMUX-` prefix. Actual native rendering, mode
restoration, key delivery and two independent client processes require live
evidence from the same Phase 2 and Phase 3 product builds.
