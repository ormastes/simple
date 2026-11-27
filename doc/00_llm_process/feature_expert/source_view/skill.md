# Source-view feature knowledge

Use `src/lib/common/source/contracts.spl` for shared byte-range/session values and `src/lib/nogc_sync_mut/source/` for deterministic projection and session transitions. The MCP adapter is `src/app/mcp/main_lazy_source_tools.spl` and is registered by `main_dispatch.spl`, `tool_table.spl` and `main_static_tools.spl`.

The new raw route is authored, not runtime-admitted. Default outline is unsupported. Do not invent an authenticated session from request prose, a workdir or an MCP transport. Preserve byte identity, whole-line continuation, SHA-256 preconditions and explicit limitations. Mutable session transitions require a serialized authenticated owner, still missing from the adapter.

Read `doc/04_architecture/tooling/source_view_foundations_2026-11-06.md`, the guide and the retained full plan before extending this foundation. Unit evidence never closes full VIEW/LANG/DBG/SEC/PERF rows by itself.

MDSOC+ public view session state (2026-11-13): the toggleable view (public default; feature_private/layer_private/all with feature/layer scope; auto-revert after 3 requests or explicit public) is the pure transition `src/lib/nogc_sync_mut/source/visibility_session.spl`, wired in `src/app/simple_lsp_mcp/visibility_state.spl` (`simple_set_visibility`) and `src/lib/nogc_sync_mut/lsp/lsp_handlers.spl` (`simple.setVisibility`). Keep it an immutable value replaced per request. Design: `doc/05_design/app/source_view/public_view_by_feature_layer.md` § Session view state; guide: `doc/07_guide/app/mcp/mcp.md` § MDSOC+ session view.
