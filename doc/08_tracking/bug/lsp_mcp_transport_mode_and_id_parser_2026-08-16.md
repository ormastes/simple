# LSP MCP transport mode and request-ID parser duplication

Status: blocked after final Rust-driver diagnostic cycle

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
