# MCP Framework — TL;DR

A complete MCP server is ~30 lines: `examples/10_tooling/minimal_mcp/`.
`mcp_server_init` + N× `mcp_server_tool(name, desc, schema_fn, handler_fn)`
+ `mcp_serve(StdioTransport.json_lines())`. Full guide: `mcp_framework.md`.

```sdn
stack {
  facade    "mcp_sdk/server/app.spl       init/tool/serve"
  registry  "mcp_sdk/server/registry.spl  lazy schemas (first tools/list)"
  transport "mcp_sdk/transport/transport  Transport trait, Stdio/Buffer"
  framing   "mcp_sdk/transport/stdio.spl  Content-Length | JSON-lines"
  plumbing  "std.net_server               TCP accept loop (future)"
}
```

- Schemas never built on `initialize` (lazy, counter-proven).
- No read timeouts — blocking is the idle state.
- `{...}` interpolates in strings: build JSON with brace helpers.
- Interpreter oracle: `printf '<init>\n<tools/list>\n' | bin/simple run app`.
- Migration: handlers+schemas → closures; delete old loop; tool-name set
  must diff empty pre/post; smoke check must stay green.
