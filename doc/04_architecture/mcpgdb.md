# mcpgdb Architecture

`mcpgdb` now uses a split example/runtime architecture:

1. Example source surface
- `examples/mcpgdb/main.spl`, `examples/mcpgdb/json_helpers.spl`, `examples/mcpgdb/protocol.spl`
- Keeps the feature discoverable under `examples/`
- Defines the public MCP shape and cold-start framing logic

2. Production runtime frontend
- `src/app/mcpgdb/main.spl`
- Cold frontend used for actual MCP execution
- Handles framing, `initialize`, `ping`, `shutdown`, `tools/list`, and `tools/call` dispatch without the example wrapper timeout

3. Debug runner family
- `src/app/mcpgdb/debug_runner.spl`, `src/app/mcpgdb/state.spl`, `src/app/mcpgdb/debug_backend_common.spl`, `src/app/mcpgdb/debug_rules.spl`, `src/app/mcpgdb/debug_tools.spl`
- Reloads persisted session metadata from `/tmp`
- Maintains explicit `DebugSession` objects across runner invocations
- Launches debugger backends as background processes connected through FIFO/log files
- Normalizes tool responses as JSON text payloads

4. Clangd runner family
- `src/app/mcpgdb/clangd_runner.spl`, `src/app/mcpgdb/state.spl`, `src/app/mcpgdb/backend_common.spl`, `src/app/mcpgdb/clangd_tools.spl`
- Reloads workspace metadata from `/tmp`
- One clangd process per workspace
- Persistent stdio framing over FIFO/log files
- Separate cache/state from debugger sessions

Safety model:
- Structured tools may perform topology changes.
- Raw command passthrough is classified into `read_only`, `execution_control`, `session_topology`, `target_mutation`, or `shell_escape`.
- `shell_escape` is blocked, `target_mutation` requires `dangerous=true`.

Runtime note:
- `src/app/mcpgdb/main.spl` is now the canonical runtime path and successfully serves `initialize`, `tools/list`, and a representative `tools/call` in this workspace.
- `examples/mcpgdb/main.spl` remains useful as example source, but it still inherits the example watchdog and is no longer the recommended runtime path.
