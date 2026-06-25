# DO NOT MAKE OTHER MCP MAIN FILES

Canonical Simple MCP entrypoint:

- `src/app/mcp/main.spl`

Rules:

- Do not add another `main_optimized.spl`, `main_lazy.spl`, `main_lite.spl`, or example-local clone for the primary `simple-mcp` server.
- Keep one root MCP main only.
- Split helper logic into sibling modules under `src/app/mcp/` when needed.
- All wrappers, plugin configs, and installer configs for the primary Simple MCP server must point to:
  - `bin/simple_mcp_server`
  - which executes `src/app/mcp/main.spl`

Allowed exceptions:

- specialized non-primary MCP servers with different product scope, such as TRACE32-specific servers
- helper modules that are imported by `src/app/mcp/main.spl`

If performance work is needed:

- optimize `src/app/mcp/main.spl`
- optimize its imported helper modules
- do not create a second primary main file
