# svim NFRs

**Feature:** svim
**Status:** Draft

## Performance

- NFR-SVIM-001: Shared-core editing operations shall update only the active buffer state and shall not require a full project scan per command.
- NFR-SVIM-002: Host TUI snapshot rendering shall operate from session state without reparsing source grammar on each frame.

## Compatibility

- NFR-SVIM-003: The public vocabulary shall remain editor-native even when MDSOC+ is used internally for decomposition.
- NFR-SVIM-004: RPC shall be message-based and compatible with the repo’s existing tool/server style.

## Reliability

- NFR-SVIM-005: Anchors shall remain deterministic across repeated insert/delete edit sequences.
- NFR-SVIM-006: Quickfix entries shall be rebuilt deterministically from buffer diagnostics.

## UX

- NFR-SVIM-007: The first shell shall visibly expose current mode, active tab/window, and cursor position.
- NFR-SVIM-008: Command execution results shall be observable through RPC responses and shell snapshot text.

## Testability

- NFR-SVIM-009: The implementation shall ship unit coverage for piece-table storage, anchor tracking, command execution, and workspace state transitions.
- NFR-SVIM-010: The implementation shall include a system-spec artifact for the host-side native-build path.
