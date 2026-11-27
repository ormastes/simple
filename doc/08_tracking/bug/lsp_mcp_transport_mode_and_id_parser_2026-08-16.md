# LSP MCP transport mode and request-ID parser duplication

Status: FIXED at tip (verified 2026-11-11, lane p3-compiler4, seed-smoke); admission of the integration spec on a built server remains lane-gated

## Failure

The LSP MCP stdio loop selected JSONL versus `Content-Length` response framing
for every request. A connection could therefore change transport mode after
startup. It also treated `Content-Length` as the only possible first framed
header, rejecting clients that send `Content-Type` first. The server bypassed
its imported canonical `extract_id` helper with a second parser, creating
divergent request-correlation behavior.

## Owner and fix

`src/app/simple_lsp_mcp/main.spl` locks JSONL when the first nonblank line starts
with `{`; every other first line selects framed header scanning. The framed
reader tolerates extension/vendor headers before `Content-Length`. Message
handling uses `json_helpers.spl::extract_id`; the duplicate parser was deleted.
Compiler discovery no longer honors the ambient `SIMPLE_BINARY` override.

## Regression contract

`test/02_integration/app/simple_lsp_mcp_stdio_spec.spl` persists two framed
requests with a leading `Content-Type` header, parses every emitted response
with `assert_all_content_length_frames`, and asserts that numeric ID `17` and
string ID `request-alpha` are preserved. Admission remains blocked until an
admitted pure-Simple runtime executes the integration spec.

The bounded Rust diagnostic native build completed with 11 modules compiled
and no stub fallback. The one permitted direct smoke exited cleanly but emitted
only one `Content-Length` response: numeric ID `17` was preserved and the
second response for string ID `request-alpha` was absent. No runtime PASS or
deployment claim is made; the lane stopped without a retry as required.

## Round 8 part 2 note 2026-11-06 (fix-implemented-verification-pending)
Seed run of `test/02_integration/app/simple_lsp_mcp_stdio_spec.spl` fails 7/7 because it needs a built server via `SIMPLE_LSP_MCP_TEST_BINARY` (not available on this host). Verify with an admitted pure-Simple build: `SIMPLE_LSP_MCP_TEST_BINARY=<built simple_lsp_mcp_server> bin/simple test test/02_integration/app/simple_lsp_mcp_stdio_spec.spl`.

## Triage 2026-11-11 (p3-compiler4 lane, batch 4 row 3) — FIXED at tip, seed-smoke verified

Both named defects are fixed in source at this lane's base, and the fix was
verified end-to-end on the interpreter (seed-smoke) without a native build:

- Transport: `json_helpers.spl:384-450` — `_TRANSPORT_MODE` is sticky per
  connection; `read_stdin_message` returns the JSONL line when the first
  nonblank line starts with `{` and otherwise tolerates any header
  (`Content-Type` included) before `Content-Length`; responses use CRLF
  framing (`Content-Length: N\r\n\r\n`).
- ID parser: the duplicate parser is gone; message handling routes through the
  canonical envelope (`main.spl:254-262`, `mcp_parse_request_envelope_v1`,
  `envelope.request_id_raw`). `extract_id` remains only as an unused helper in
  json_helpers.spl:219.
- Seed-smoke: piped two framed requests down one connection — first with a
  leading `Content-Type` header, numeric id 17; second string id
  "request-alpha". Output: two well-formed `Content-Length` frames with
  `\r\n\r\n` separators, ids preserved exactly (`{"jsonrpc":"2.0","id":17,...}`
  and `{"jsonrpc":"2.0","id":"request-alpha",...}`).

Admission caveat: the integration spec
`test/02_integration/app/simple_lsp_mcp_stdio_spec.spl` still requires a built
server via `SIMPLE_LSP_MCP_TEST_BINARY`; this lane is barred from entry-closure
native builds, so that admission run remains for the owner lane. The defect
itself is verified fixed.
