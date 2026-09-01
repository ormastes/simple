# HIR callable-dep diagnostic fabricates name/position for bare `fn()` types

**Filed:** 2026-08-29 (debug_service_v1 Opus verification)
**Status:** OPEN

Native build reports `unresolved name: signal|mcp_run_argv|mcp_server_init`
at (file,line,col) triples that do not match file content. Root: the bare
`fn()` callable type in `std.nogc_sync_mut.io.signal_stubs.signal_handler_install`
— log line `[hir-callable-dep-origin-unresolved] owner=...signal_stubs dependency=fn`
— is reported with a fabricated name/location against unrelated modules
(src/app/mcp/main.spl:24:8 etc.). One defect, not three; no import binding can
fix it; needs the HIR callable-dependency diagnostic (and possibly resolution
of bare `fn` types) fixed in the compiler. Last blocker for a clean native MCP
build (10 error lines). Evidence: $SCRATCHPAD/VERIFY_debug_service.md §3.
