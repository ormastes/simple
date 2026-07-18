# MCP Local Handshake Evidence - 2026-06-11

## Scope

This report records the local deployment check for the Simple MCP and Simple LSP MCP servers.

The local Codex MCP configuration points to:

- `/home/ormastes/dev/pub/simple/bin/simple_mcp_server`
- `/home/ormastes/dev/pub/simple/bin/simple_lsp_mcp_server`

Both launchers resolve cached native binaries from `build/bootstrap/mcp-package/`.
Raw runtime or source-entry execution was not used for the deployment check.

## JSONL handshake

Requests: `initialize`, then `tools/list`.

| Server | Result | Elapsed | Bytes | Evidence |
| --- | --- | ---: | ---: | --- |
| Simple MCP | `rc=0`, initialize ok, tools ok | 1354.4 ms | 38665 | `play_wm_text_status`, `debug_create_session` present |
| Simple LSP MCP | `rc=0`, initialize ok, tools ok | 38.6 ms | 5454 | `lsp_definition` present |

## Content-Length framed handshake

Requests: framed `initialize`, `notifications/initialized`, then framed `tools/list`.

| Server | Result | Elapsed | Frames | Bytes | Evidence |
| --- | --- | ---: | ---: | ---: | --- |
| Simple MCP | `rc=0`, framed ok | 1908.8 ms | 2 | 38665 | `play_wm_text_status`, `debug_create_session` present |
| Simple LSP MCP | `rc=0`, framed ok | 41.9 ms | 2 | 5495 | `lsp_definition` present |

## Wrapper overhead check

Three warm runs compared wrapper launch against direct cached native binary launch.

| Server | Wrapper elapsed | Native elapsed | Result |
| --- | --- | --- | --- |
| Simple MCP | 1463.8 ms, 1422.9 ms, 1422.6 ms | 1384.7 ms, 1303.4 ms, 1634.7 ms | Wrapper overhead is not the dominant cost |
| Simple LSP MCP | 46.7 ms, 40.3 ms, 32.1 ms | 18.6 ms, 18.8 ms, 22.8 ms | Wrapper overhead is about 20 ms |

## Conclusion

Local deployment is configured through the production wrappers and cached native MCP artifacts.
The Simple MCP and Simple LSP MCP servers both complete JSONL and Content-Length framed handshakes
without using raw runtime or source-entry execution.
