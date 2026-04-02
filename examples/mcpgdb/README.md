# mcpgdb

Merged C/C++ debug MCP example for this repo.

The shipped shape is now a cold frontend in `main.spl` plus family-specific subprocess runners:
- `main.spl` handles framing, `initialize`, `ping`, `shutdown`, and `tools/list`
- `tools/call` dispatches to `debug_runner.spl` or `clangd_runner.spl`
- session and workspace metadata are persisted in `state.spl` under `/tmp`

It provides:
- persistent multi-session debugger control for `gdb`, `lldb`, `openocd_gdb`, and `t32_gdb`
- gated raw debugger commands with backend-specific safety rules
- workspace-scoped clangd tools for definition, references, hover, symbols, completion, type definition, and `clangd --check` diagnostics
- `clangd_open` for starting the workspace language server explicitly
- `debug_disconnect` and `debug_restart` alongside the main execution-control tools
- mutable register and memory tools for the current session

## Run

```bash
bin/simple run examples/mcpgdb/main.spl
```

Optional environment variables:
- `GDB_BINARY`
- `LLDB_BINARY`
- `CLANGD_BINARY`

## Example MCP flow

1. `workspace_open(root: "/path/to/project")`
2. `clangd_open(root: "/path/to/project")`
3. `debug_session_create(backend: "gdb")`
4. `debug_launch(session_id: "dbg_1", program: "/path/to/app")`
5. `breakpoint_set(session_id: "dbg_1", file: "src/main.cpp", line: "42")`
6. `debug_continue(session_id: "dbg_1")`

For OpenOCD or TRACE32 GDB backends, create the session with `openocd_gdb` or `t32_gdb`, then use `debug_connect_remote`.

Current runtime note: `initialize` now succeeds under the repo watchdog, but the first heavy `tools/call` path can still exceed the 4GB/10s example watchdog while the runner path is compiled in this workspace. The public tool names are unchanged; the remaining work is runtime tuning of the heavy runner compile path.
