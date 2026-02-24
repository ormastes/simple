# DAP + MCP Variable-Change Breakpoints Plan (2026-02-24)

## Goal
Implement variable-change breakpoints (data breakpoints/watchpoints) across DAP and MCP with explicit capacity policy for host vs bare-metal targets.

## Gap
- DAP advertised no data-breakpoint capability.
- DAP did not handle `dataBreakpointInfo` or `setDataBreakpoints`.
- MCP debug tools had line/function breakpoints only; no dedicated variable-change breakpoint API.
- No explicit response contract for capacity-exceeded behavior on constrained hardware targets.

## Design
- Host/interpreter mode: high-capacity software watchpoints (default 1024).
- Bare-metal/remote mode: conservative low-capacity hardware watchpoints (default 1) because hardware slots may be shared by loader/scripts.
- DAP capacity overflow behavior: return per-breakpoint `verified:false` with message.
- MCP capacity overflow behavior: tool-level error with clear limit message.

## Implemented
### DAP
- Capabilities:
  - `supportsDataBreakpoints: true`
  - `supportsSetVariable: true`
- Added commands:
  - `dataBreakpointInfo`
  - `setDataBreakpoints`
  - `setVariable`
- Added runtime state:
  - active data breakpoints
  - next data breakpoint id
  - max data breakpoint capacity
- Added trigger behavior:
  - on `setVariable`, emit `stopped` event with reason `data breakpoint` when watched variable value changes.

- Remote backend integration:
  - `setDataBreakpoints` now attempts target watchpoint install via remote backend (GDB/Trace32) and reports unverified entries on target failure.
  - Capacity is now dynamic when remote backend is active (`watchpoint_capacity()` from target metadata).

### MCP (main_lazy)
- Added tools:
  - `debug_set_data_breakpoint`
  - `debug_list_data_breakpoints`
  - `debug_remove_data_breakpoint`
- Added per-session data-breakpoint state.
- Implemented in both MCP paths: `main_lazy` and `app.mcp.debug_tools` (handler/adapter wiring updated).
- Added variable-change trigger path in `debug_set_variable`:
  - returns `data_breakpoint_hit` and `hit_breakpoint_ids`.
- Added target-aware capacity policy helper.
- Added schema and annotations for new tools.

## Response Format Notes
- DAP: per-item success/failure in `setDataBreakpoints` response; failure uses `verified:false` and message.
- MCP: normal `content` + `structuredContent` tool result style retained.

## Tests
- Updated MCP protocol matrix/runtime specs to include new debug data-breakpoint tool exposure and counts.
- Verified MCP probes (Python/TypeScript/Rust) still pass.
- Verified DAP unit protocol/server specs pass.

## Remaining Work
- Bind DAP data-breakpoint hit path to real runtime memory/variable mutation events (beyond `setVariable` simulation).
- Expose target-reported watchpoint counts dynamically (instead of fixed defaults).
- Add end-to-end DAP spec for `setDataBreakpoints` + `setVariable` stop event assertions.
