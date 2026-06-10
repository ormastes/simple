# Plan: Std Network-Server Lib + MCP Framework + MCP App Migration

Date: 2026-06-10
Status: planned (executes after host-io layering Wave 2; see
`doc/03_plan/lib/host_io_layering/plan.md`)
Goal: make writing an MCP server in Simple *easy* (declarative builder, one
import) and *fast* (startup ladder steps 2–6 built into the framework), then
move every in-repo MCP server onto it.

## Ground truth (researched 2026-06-10)

- `src/lib/nogc_sync_mut/mcp_sdk/` already has core (jsonrpc, types, json,
  validation, errors), server (builder 163L, router 190L, state, pagination,
  method_detect), transport (stdio framing, auto Content-Length/JSON-lines).
- `src/app/simple_lsp_mcp` already consumes mcp_sdk; **`src/app/mcp` does
  not** — it hand-rolls its loop (`main.spl` + 9 `main_lazy_*` modules,
  151 tools, 1361 ms handshake).
- `src/lib/nogc_sync_mut/http_server/` has handler/middleware/parser/
  response/router — the route-dispatch shape to mirror, not reinvent.
- `src/lib/nogc_sync_mut/io/tcp.spl` has TcpListener.accept/accept_timeout;
  `std.nogc_async_mut.host_io.net` (Wave 1) adds async wrappers.
- Startup levers T4a (wrapper probe cache) and T4b (lazy tool registry) are
  framework features, not app patches:
  `doc/07_guide/app/mcp/startup_performance.md`.

## Design rules

- D1 Framework = finish + adopt `mcp_sdk`; no parallel new SDK. New modules
  live under `mcp_sdk/` (sync core) and use `host_io` for transport I/O.
- D2 Server definition is declarative and lazy:
  `McpServer(name, version).tool(spec, handler)...serve_stdio()` — tool
  *schemas* are not constructed until first `tools/list` (T4b); `initialize`
  answers from static metadata.
- D3 Transports are pluggable behind one trait (stdio now; tcp via
  net-server lib; http/sse later). Stdio reads block forever — no timeouts.
- D4 Net-server lib is transport plumbing only (accept loop, connection
  lifecycle, dispatch callback); protocol logic stays in mcp_sdk/http_server.
- D5 Apps own only tool handlers + wiring. No framing, no registry plumbing,
  no rt_* (gates already enforce this).

## Waves (each task sized for one Sonnet agent, disjoint file scopes)

### Wave A — net-server lib + framework core (parallel, 4 agents)

- A1 `std.net_server` (`src/lib/nogc_sync_mut/net_server/{listener.spl,
  connection.spl}` + unit spec): generic accept-serve loop over
  tcp.TcpListener with a `ConnectionHandler` callback trait; graceful stop;
  loopback echo spec. No protocol logic.
- A2 `mcp_sdk/server/registry.spl` (+ spec): lazy ToolRegistry — register
  (name, summary, schema-builder closure, handler); schemas built on first
  `tools/list`, memoized; pagination preserved. This is T4b.
- A3 `mcp_sdk/transport/transport.spl` (+ spec): Transport trait
  (read_message/write_message/close) + StdioTransport adapter over the
  existing stdio framing; prep TcpTransport stub wired to A1 (compile-only
  until Wave C).
- A4 `mcp_sdk/server/app.spl` (+ spec): the `McpServer` facade tying
  builder+router+registry+transport into `serve(transport)`, with framed
  initialize/tools-list/tools-call golden-transcript spec (absolute oracle:
  exact JSON fields, not just "no error").

### Wave B — startup levers in wrappers (parallel with Wave A, 1 agent)

- B1 T4a probe cache: wrapper generator in scripts/setup emits probe-stamp
  logic (`.simple/cache/mcp-probe/<sha-of-path>.stamp` keyed by binary
  mtime+size); `check-mcp-native-smoke.shs` gains assertions that (a) second
  start skips probe, (b) startup_ms improves ~2x, (c) stale stamp re-probes.

### Wave C — migrate apps (after A lands; parallel, disjoint app dirs)

- C1 `src/app/mcp` onto McpServer + lazy registry (the 151-tool surface;
  biggest win; keep `main_lazy_*` handler bodies, delete hand-rolled loop).
- C2 `src/app/simple_lsp_mcp` aligned to McpServer facade (already on
  mcp_sdk; smallest diff first — use as the migration template).
- C3 `src/app/mcpgdb`, `src/app/serial_mcp`, `src/app/ui.mcp` onto the
  framework.
- Gate per app: `check-mcp-native-smoke.shs` green; tools_count unchanged;
  startup_ms not worse; direct-rt gates stay true.

### Wave D — proof + docs (1 agent + orchestrator)

- D1 Example: `examples/10_tooling/minimal_mcp/` — a complete MCP server in
  ~30 lines using the framework (the "easy" proof).
- D2 Guide `doc/07_guide/app/mcp/mcp_framework.md` + tldr; update mcp.md and
  the host-io plan cross-links.

## Acceptance

- AC-1 New MCP server expressible in ≤30 lines (D1 compiles + handshakes).
- AC-2 `initialize` path constructs zero tool schemas (registry spec proves
  lazy build; instrumented counter, not timing).
- AC-3 Wrapper second-start ≤ 60% of first-start (probe cache, measured in
  smoke check).
- AC-4 All five MCP apps on the framework; smoke check green; tools_count
  identical before/after migration.
- AC-5 No duplicated framing/json/registry code left in src/app/* (semantic
  dup scan over migrated apps).

## Known interpreter issues hit during Wave A (concrete bugs, not folklore)

- BUG-1 `match Some(i): idx = i` silently fails to bind/assign to an outer
  var in interpreter mode (no error, stale value). Hit in A4; worked around
  with `== nil` guards + direct-return unwrap helpers and `has_method`
  string dispatch. Needs an interpreter-lane fix + regression spec.
- BUG-2 `rt_io_udp_bind` not registered in interpreter mode via the
  `nogc_async_mut → nogc_sync_mut/io/udp` chain (see host_io plan §4a).
- BUG-3 `BufferTransport.read_message` trait-impl shape: a `fn` stub
  satisfying the trait while the real logic sat in a separate `me` method
  compiled clean but never executed — trait conformance does not flag
  unreachable split impls. Caught only by the spec's absolute oracle.

## Ordering & risks

- A and B are independent; C depends on A; D last. C1 is the riskiest
  (151 tools) — do C2 first as template, then C1/C3 in parallel.
- Interpreter-mode extern hang on stdin: transports keep extern decls in the
  same compiled-mode-only pattern the current stdio module uses.
- jj parallel-commit clobber: orchestrator commits per agent batch by path.
