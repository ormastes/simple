# mcpgdb Architecture

`examples/mcpgdb` now uses a cold frontend with family-specific subprocess runners:

1. Cold MCP frontend
- `main.spl`, `json_helpers.spl`, `protocol.spl`
- Handles framing, `initialize`, `ping`, `shutdown`, `tools/list`, and `tools/call` dispatch
- Keeps startup light so `initialize` stays under the watchdog

2. Debug runner family
- `debug_runner.spl`, `state.spl`, `backend_common.spl`, `debug_rules.spl`, `debug_tools.spl`
- Reloads persisted session metadata from `/tmp`
- Maintains explicit `DebugSession` objects across runner invocations
- Launches debugger backends as background processes connected through FIFO/log files
- Normalizes tool responses as JSON text payloads

3. Clangd runner family
- `clangd_runner.spl`, `state.spl`, `backend_common.spl`, `clangd_tools.spl`
- Reloads workspace metadata from `/tmp`
- One clangd process per workspace
- Persistent stdio framing over FIFO/log files
- Separate cache/state from debugger sessions

Safety model:
- Structured tools may perform topology changes.
- Raw command passthrough is classified into `read_only`, `execution_control`, `session_topology`, `target_mutation`, or `shell_escape`.
- `shell_escape` is blocked, `target_mutation` requires `dangerous=true`.

Runtime note:
- The cold frontend now starts cleanly, but the first heavy `tools/call` still pays the cost of compiling the runner path in this workspace and can trip the 4GB/10s example watchdog.
