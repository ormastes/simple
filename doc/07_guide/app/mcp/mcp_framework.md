# MCP Framework Guide (`std.mcp_sdk` McpServer facade)

Date: 2026-06-10. Status: Waves A/B + C2/C3 landed; see
`doc/03_plan/app/mcp_framework/plan.md`.

## Writing a server

The complete working example is
`examples/10_tooling/minimal_mcp/minimal_mcp.spl` (~30 lines):

```simple
use std.mcp_sdk.server.app.{mcp_server_init, mcp_server_tool, mcp_serve}
use std.mcp_sdk.transport.transport.{StdioTransport}

fn main():
    mcp_server_init("my-server", "0.1.0")
    mcp_server_tool("echo", "Echo arguments.", echo_schema, echo_handler)
    mcp_serve(StdioTransport.json_lines())
```

- `schema_builder: fn() -> text` returns the inputSchema JSON. It is called
  at most once, on the FIRST `tools/list` — never during `initialize`
  (startup ladder step 4; proven by `registry_schemas_built()`).
- `handler: fn(text) -> text` receives the raw arguments JSON object and
  returns the tool result text (wrapped into the JSON-RPC envelope for you).
- `mcp_serve` blocks reading the transport until it yields nil. There are NO
  timeouts anywhere in the read path — blocking is the correct idle state.

## Layer map

| Layer | Module | Job |
|-------|--------|-----|
| facade | `mcp_sdk/server/app.spl` | init/tool/handle/serve dispatch |
| registry | `mcp_sdk/server/registry.spl` | lazy memoised schemas, tools/call |
| transport | `mcp_sdk/transport/transport.spl` | `Transport` trait; `StdioTransport` (real framing), `BufferTransport` (tests) |
| framing | `mcp_sdk/transport/stdio.spl` | Content-Length / JSON-lines auto-detect |
| plumbing | `std.net_server` | generic TCP accept-serve loop (future TcpTransport) |

Apps own only tool handlers + wiring (plan rule D5). The `rt_*` rg gates in
`check-mcp-native-smoke.shs` enforce that app dirs stay facade-only.

## Gotchas (each cost an agent real time)

- `{...}` in string literals is interpolation: inline JSON literals get
  mangled silently. Build JSON with brace-helper fns (`lb()`/`rb()`/`jp`)
  — see the example and `src/app/serial_mcp/main.spl`.
- BUG-1: `match Some(x):` assigning an outer var silently no-ops in
  interpreter mode — use `== nil` guards and direct-return helpers.
- BUG-3: a trait method satisfied by a `fn` stub while the real logic sits
  in a separate `me` method compiles clean and never runs. Always pin
  behavior with a spec oracle (BufferTransport golden transcript).
- BUG-4: native codegen currently fails (`undefined symbol: range`), so the
  execution oracle for migrations is the piped interpreter handshake:
  `printf '<initialize>\n<tools/list>\n' | bin/simple run <app>/main.spl`.

## Testing pattern

Unit: drive `mcp_server_handle`/`mcp_serve` through
`BufferTransport.with_messages([...])` and assert EXACT response fields
(`test/01_unit/lib/mcp_sdk/app_spec.spl` is the model; equality alone is not
correctness — assert serverInfo values, tool names, -32601 codes).
Integration: piped interpreter handshake + `check-mcp-native-smoke.shs`
(tools_count, framing, schema validity, startup gates, probe-cache gates).

## Migration recipe (from the C2/C3 migrations)

1. Each tool's schema code → `fn() -> text` closure; dispatch branch →
   `fn(text) -> text` handler.
2. Replace the hand-rolled read/detect/dispatch/write loop with
   init + registrations + `mcp_serve`.
3. Delete the old loop, method detection, tools-list/init builders, caches —
   no dual dispatch paths.
4. Verify: interpreter check, piped handshake with IDENTICAL tool-name set
   (diff sorted lists pre/post), rt_ rg gate, smoke check exit 0.

## Startup properties

Wrapper probe results are cached by binary mtime+size
(`.simple/cache/mcp-probe/`); `initialize` builds zero schemas; see
`startup_performance.md` for the full ladder and measurements.
