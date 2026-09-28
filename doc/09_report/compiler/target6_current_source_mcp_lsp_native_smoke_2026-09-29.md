# Target 6 current-source MCP/LSP native smoke

Status: focused native request smoke PASS; full compiler cutover and paired
performance qualification remain open.

The Stage2 pure-Simple capsule built `src/app/simple_lsp_mcp/main.spl` from this
worktree with `SIMPLE_NO_STUB_FALLBACK=1`, entry closure, and the hosted runtime
bundle: 12 compiled units, 0 failed, 1.55 seconds build time, 134,900 KiB
build peak RSS, and a 133,752-byte stripped executable. The earlier
current-source `src/app/mcp/main.spl` native build produced an 899,608-byte
stripped executable.

A JSON-RPC `ping` reached the native LSP server. The first `lsp_symbols` tool
call returned a process error because this isolated worktree has no
`bin/simple`. Supplying the immutable Stage2 capsule through `SIMPLE_BINARY`
also failed: that capsule does not admit the LSP query script as an implicit
command. With `SIMPLE_BINARY=/home/yoon/dev/simple/bin/simple`, the native
server returned a nonempty symbol list for
`src/app/simple_lsp_mcp/main.spl`, including `SERVER_NAME`; exit code was 0
and stderr was empty. The subprocess uses the installed self-hosted runtime,
so this is not proof of a current-source query-engine build.

The current-source native MCP server accepted JSON-RPC `initialize` and a
`simple_status` tool call for `src/app/mcp/main.spl`. It returned protocol
version `2025-06-18`, `serverInfo.name=simple-mcp-full`, and a tool result with
`isError=false` and one queued candidate file; exit code was 0 and stderr was
empty. This proves request dispatch, not completed diagnostics or Target 6
warm-index routing.

Neither smoke measures warm compiler time, peak RSS on a realistic compile
fixture, or the pinned package-index production path. Those remain release
gates alongside the full current-source CLI cutover.
