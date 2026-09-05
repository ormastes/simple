# mcpgdb Local Research

Feature: merged debugger and clangd MCP example under `examples/mcpgdb`.

Local findings:
- `examples/korean_stock_mcp` is the minimal self-contained MCP example pattern.
- `src/app/simple_lsp_mcp` is the cleaner transport/schema pattern for MCP protocol handling.
- `examples/10_tooling/trace32_tools/t32_mcp` demonstrates explicit multi-session state, tool routing, lazy backend setup, and file-backed helper processes.
- The runtime exposes subprocess execution, file offset reads, FIFO-friendly filesystem primitives, and temp-dir management, but not direct bidirectional child-process handles.

Implementation implication:
- Persistent backend control has to be built around shell-launched background processes plus FIFO/log files.
- Multi-session support is feasible in-process with explicit `session_id`.
- clangd is feasible as one workspace-scoped background process using stdio framing over FIFO/log files.
