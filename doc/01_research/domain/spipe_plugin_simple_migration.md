# Domain Research: SPipe Plugin Simple-Language Migration

Date: 2026-09-24. External prior art for migrating a Node.js CLI + MCP server
to a self-hosted language runtime (Simple).

## MCP stdio transport and JSON-RPC requirements

- MCP encodes messages as JSON-RPC 2.0, UTF-8, over two standard transports;
  stdio is "newline-delimited messages over the standard streams of a
  client-launched subprocess" (spec:
  https://modelcontextprotocol.io/specification/2026-07-28/basic/transports).
  No Content-Length headers — LSP-style framing is obsolete and breaks
  current clients (https://github.com/jnuyens/gsd-plugin/issues/3).
- Protocol versions evolve (`2024-11-05`, `2025-03-26`, `2025-06-18`,
  ...); `initialize` negotiates by echoing a supported version. The Node
  server pins `2024-11-05`; `std.mcp_sdk` answers `2025-06-18` — a version
  bump the migration should explicitly accept (clients take the server's
  echoed version).
- stdio servers MUST NOT log to stdout (stdout is the wire); diagnostics go
  to stderr. JSON-RPC error codes: -32700 parse, -32600 invalid request,
  -32601 method not found, -32602 invalid params, -32603 internal. The Node
  server uses nonstandard -32000 — moving to the SDK's standard codes is an
  acceptable, spec-conformant behavior change.
- Windows pitfall: CRLF translation corrupts NDJSON framing
  (https://github.com/modelcontextprotocol/python-sdk/issues/2433). Any
  Simple stdio writer must emit `\n` verbatim; `print_raw` (used by
  src/app/mcp) avoids translation — verify on Windows in the plan.
- Hand-rolled NDJSON loop guidance (buffer, split on `\n`, one parse error
  must not poison subsequent lines):
  https://aiengineeringfromscratch.com/lesson?path=phases%2F19-capstone-projects%2F22-jsonrpc-stdio-transport
  and https://imti.co/mcp-why-the-wire/.

## Node → custom-runtime CLI migration considerations

Per capability, and how Simple covers it:
- Argument parsing: Node uses `process.argv` + manual switch. Simple CLI
  apps use `get_args`/`cli_arg_at` with the same manual-dispatch idiom
  (src/app/mcp/main.spl:79-80, src/app/cli_parser.spl) — a direct port,
  no getopt library needed for positional subcommand CLIs.
- JSON emit/parse: Node `JSON.stringify/parse`. Simple has
  `std.mcp_sdk.core.json` (`jp`, `js`, `jo3`, `escape_json`) and
  `std.js.builtins.json` — sufficient for the 6-tool static surface.
- stdio: Node line-buffered stdin events. Simple: `extern stdin_read_char`
  + `print_raw` idiom, already proven in src/app/mcp.
- File I/O: Node fs sync calls map 1:1 onto std.io_runtime file/dir
  helpers. Registry-append pattern (appendFileSync of SDN blocks) maps to
  `file_append_text`.
- Process spawning: the CLI spawns nothing except via users' recorded
  command strings (stored, not executed) — `process_run` covers doctor-era
  checks if needed.
- Symlinks/junctions on Windows: Node `symlinkSync` needs privileges on
  Windows for symlink privileges vs junctions. Simple stdlib has NO symlink
  API (see local research gap). Prior art: keep link creation in the
  existing POSIX sh / PowerShell setup scripts (junctions on Windows,
  symlinks on POSIX) and treat in-process link creation as best-effort via
  shell delegation.

## Staging strategies for CLI rewrites (prior art)

- Strangler Fig / branch-by-abstraction: route command-by-command from the
  old implementation to the new behind a stable dispatch facade; run both in
  parallel and diff outputs (https://oneuptime.com/blog/post/2026-01-30-strangler-fig-pattern/view,
  https://milanjovanovic.tech/blog/strangler-fig-modular-monolith-migration).
- Recommended shape for this migration: keep `cli/spipe.js` and
  `mcp/server.js` in the repo during transition; the `.spl` CLI handles the
  ported subcommand set and either errors or delegates on the rest; a
  golden-output parity harness diffs Node vs Simple output per subcommand in
  CI. Remove Node only after parity is green — avoids the "big rewrite gets
  abandoned" failure mode.
- MCP server rewrites are far smaller (187 lines here) and SDK-supported;
  comparable projects rewrite the server outright and validate with a
  4-message scripted handshake (initialize / notifications/initialized /
  tools/list / tools/call) — exactly what `scripts/build.sh:56-57` already
  pipes today.
