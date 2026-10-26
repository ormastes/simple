# CoreMux capture controls

Status: **NOT_RUN**. Authored companion; no runner execution, generated manual,
maintenance score, measured coverage, or native-provider qualification.

Source: `test/01_unit/os/smux_capture_cursor_spec.spl`.

The controls invoke the production VT parser, PaneRecord and capture owner with
explicit values. Constructed lease IDs and native-handle numbers are test data;
they do not acquire a native resource or authenticate a connected client.

| Requirement | Behavior checked |
| --- | --- |
| REQ-CMUX-005 | Logical Screen/AllHistory/Lines selection, negative screen-relative offsets and wrap joining |
| REQ-CMUX-005; NFR-CMUX-007 | Retained history SGR and exact concatenation of UTF-8/ANSI byte pages |
| REQ-CMUX-008; NFR-CMUX-006 | Lease separation, content/incarnation staleness, option mismatch, expiry, consumed-token replay |
| REQ-CMUX-006; NFR-CMUX-005 | At most 16 retained descriptors; revocation frees descriptors |
| REQ-CMUX-003; NFR-CMUX-007 | Consumed original bytes advance ingestion independently of content; queries and same-cell writes preserve content revision |
| REQ-CMUX-008; NFR-CMUX-008 | Frozen cells/styles/history/wraps remain stable; deferred-handle values retain ownership and incarnation |

Source cycle 2 adds independent Han/emoji UTF-8 and SGR expected byte vectors;
legacy pipe history beyond the grid; CSI discard/resynchronization; a 1 MiB
Unicode-safe tail suffix; and combining-cell loss/recovery by overwrite, erase,
history eviction and synchronized release. These remain NOT_RUN.

CSI parameters and combining cells retain at most 256 UTF-8 bytes. Oversized CSI
resynchronizes without disabling capture. Lost combining content marks only its
retained cell; strict capture fails only for affected selected rows until that
content is removed. Ordinary tail eviction is reported by `tail_truncated` and
does not promise pagination into discarded history. Selected requirements are
REQ-CMUX-003/005/006/008 and NFR-CMUX-005/006/007/008.

The terminal snapshot serializes every retained cell, including spaces. Plain
output uses line separators; styled output uses canonical SGR transitions.
`join_wrapped` removes only soft-wrap separators and never changes logical-line
selection. Clients concatenate all byte pages before decoding UTF-8 or SGR.

The separate `coremux_capture_native_spec.spl` scenario uses a real ConPTY child.
Neither authored spec is evidence of a passing run.
