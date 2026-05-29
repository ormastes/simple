# mcpgdb Feature Requirements

- Provide a runnable MCP example at `examples/mcpgdb`.
- Support multiple concurrent debug sessions with explicit `session_id`.
- Support `gdb`, `lldb`, `openocd_gdb`, and `t32_gdb` backend kinds.
- Expose structured tools for session lifecycle, execution control, breakpoints, frames, variables, registers, memory, and remote attach/connect.
- Expose a raw debugger command tool gated by backend-aware command rules.
- Expose clangd-backed workspace tools in the same MCP server.
- Keep the server usable without native TRACE32 GUI/session features; TRACE32 support is through its GDB backend in this example.
