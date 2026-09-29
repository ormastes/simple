# Target 6 core and MCP smoke follow-up

Status: core runtime smoke PASS; current-source MCP native build PASS;
MCP/LSP request smoke and production qualification pending.

The core runtime smoke script's compile step still expected the evaluated
value `42` in the compiler's status line. The compiler reports
`Compiled <source> -> <artifact>` instead. Eval and source execution already
assert `42`; the compile step now requires that status and a nonempty SMF
artifact. `sh scripts/check/check-core-runtime-smoke.shs
/home/yoon/dev/simple/bin/simple` reports all four checks true.

The existing MCP wrappers launched raw source through the installed binary.
Its JIT could not resolve `rt_file_read_regular_no_follow_bounded_bytes`, so
that wrapper run did not qualify the current worktree. A no-stub Stage2
entry-closure build of `src/app/mcp/main.spl` initially failed HIR field
inference at `dap_bridge.spl`'s mutable backend capabilities. Explicitly
typing the backend and importing the debug session model directly from its
owner allowed the current-source MCP server to link: 121 units compiled, 0
failed, 3.52 seconds, 413,876 KiB peak build RSS, 878 KiB stripped binary.

The resulting binary has not yet passed initialize/request smoke. Build a
current-source LSP MCP binary and run both through the native smoke gate
before claiming MCP/LSP startup qualification. The core smoke used the
installed runtime; it is not a performance measurement of the changed
compiler branch.
