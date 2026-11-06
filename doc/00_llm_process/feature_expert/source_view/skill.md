# Source-view feature knowledge

Use `src/lib/common/source/contracts.spl` for shared byte-range/session values and `src/lib/nogc_sync_mut/source/` for deterministic projection and session transitions. The MCP adapter is `src/app/mcp/main_lazy_source_tools.spl` and is registered by `main_dispatch.spl`, `tool_table.spl` and `main_static_tools.spl`.

The new raw route is authored, not runtime-admitted. Default outline is unsupported. Do not invent an authenticated session from request prose, a workdir or an MCP transport. Preserve byte identity, whole-line continuation, SHA-256 preconditions and explicit limitations. Mutable session transitions require a serialized authenticated owner, still missing from the adapter.

Read `doc/04_architecture/tooling/source_view_foundations_2026-11-06.md`, the guide and the retained full plan before extending this foundation. Unit evidence never closes full VIEW/LANG/DBG/SEC/PERF rows by itself.
