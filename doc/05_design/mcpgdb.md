# mcpgdb Detail Design

Data model:
- `DebugSession`: backend kind, process pid, FIFO/log paths, current thread/frame, workspace root
- `WorkspaceState`: root, compile commands dir, clangd pid, stdio files, request sequencing
- Session and workspace metadata are serialized to `/tmp` so the cold frontend can stay stateless across `tools/call` subprocesses

Control flow:
- `examples/mcpgdb/main.spl` remains the example/frontend source shape, but `src/app/mcpgdb/main.spl` is the canonical runtime entrypoint.
- `src/app/mcpgdb/main.spl` is cold at startup and never imports the heavy runner families.
- `tools/call` selects `src/app/mcpgdb/debug_runner.spl` or `src/app/mcpgdb/clangd_runner.spl`, passes the request body through a temp file via `MCPGDB_REQUEST_PATH`, and returns the runner's JSON-RPC response.
- `src/app/mcpgdb/debug_runner.spl` reloads session metadata, allocates or reuses debugger processes, and routes structured debug tools through the shared session command runner.
- `debug_command_run` passes through the rule engine before writing to the backend FIFO.
- `src/app/mcpgdb/clangd_runner.spl` reloads workspace metadata, launches clangd on demand, and serves the clangd tool family.
- Clangd position tools ensure the file is opened, then send JSON-RPC requests and return the raw response body.

Known limitations in v1:
- Debugger structured tool outputs are normalized JSON text wrappers around backend CLI output rather than deeply parsed typed objects.
- clangd diagnostics use `clangd --check` while the other clangd tools use the persistent workspace process.
- The `examples/mcpgdb/main.spl` wrapper still inherits the example watchdog, so end-to-end runtime validation should use `src/app/mcpgdb/main.spl`.
