# mcpgdb Detail Design

Data model:
- `DebugSession`: backend kind, process pid, FIFO/log paths, current thread/frame, workspace root
- `WorkspaceState`: root, compile commands dir, clangd pid, stdio files, request sequencing
- Session and workspace metadata are serialized to `/tmp` so the cold frontend can stay stateless across `tools/call` subprocesses

Control flow:
- `main.spl` is the cold frontend and never imports the heavy runner families at startup.
- `tools/call` selects `debug_runner.spl` or `clangd_runner.spl`, passes the request body through a temp file, and returns the runner's JSON-RPC response.
- `debug_runner.spl` reloads session metadata, allocates or reuses debugger processes, and routes structured debug tools through the shared session command runner.
- `debug_command_run` passes through the rule engine before writing to the backend FIFO.
- `clangd_runner.spl` reloads workspace metadata, launches clangd on demand, and serves the clangd tool family.
- Clangd position tools ensure the file is opened, then send JSON-RPC requests and return the raw response body.

Known limitations in v1:
- Debugger structured tool outputs are normalized JSON text wrappers around backend CLI output rather than deeply parsed typed objects.
- clangd diagnostics use `clangd --check` while the other clangd tools use the persistent workspace process.
- The first heavy `tools/call` in this workspace can still hit the 4GB/10s example watchdog while the runner path is compiled, even though `initialize` is now cold and succeeds.
