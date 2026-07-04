# MCP Framework Plan — TL;DR

Make MCP servers easy (declarative, one import) and fast (startup ladder
built in), then migrate all five in-repo MCP apps. Framework = finish and
adopt `mcp_sdk`, not a new SDK. Full plan: `plan.md`.

```sdn
waves {
  A net_server_lib_and_framework_core {  # 4 parallel agents
    A1 "std.net_server accept-serve loop (transport plumbing only)"
    A2 "mcp_sdk lazy ToolRegistry — schemas on first tools/list"
    A3 "Transport trait + StdioTransport (blocking, no timeout)"
    A4 "McpServer facade + golden-transcript spec"
  }
  B wrapper_probe_cache "stamp by binary mtime+size; ~2x startup win"
  C migrate_apps "C2 lsp (template) -> C1 mcp(151 tools) + C3 rest"
  D proof_and_docs "30-line example server + guide"
}
```

Acceptance: ≤30-line example server; zero schemas built on `initialize`;
second wrapper start ≤60% of first; all apps migrated with identical
tools_count and green `check-mcp-native-smoke.shs`.
