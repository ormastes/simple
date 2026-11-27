# Source-view foundations

<!-- codex-architecture -->

Status: implementation authored; runtime admission and full-plan acceptance remain open.

The selected MCP/LSP source-debugging plan is retained under `doc/03_plan/release/1.0.0/inputs_2026-11-06/`. This incremental implementation does not replace its full acceptance matrix.

`src/lib/common/source/contracts.spl` owns byte-range, projection and session values without filesystem, compiler or UI dependencies. `src/lib/nogc_sync_mut/source/projection.spl` selects exact ordered source ranges and records omissions. `session.spl` implements value transitions; an authenticated host must serialize and commit them. The current MCP composition root has no such logical-agent authority, so the handler explicitly reports that session isolation is unavailable. No client-provided session ID becomes authorization.

`src/app/mcp/main_lazy_source_tools.spl` is a lazy protocol adapter. The dispatcher, full tool table and static discovery table register `source_open`. It accepts explicit raw mode only. Default outline requests return `unsupported` rather than silently dumping a file. Missing outline providers, semantic analysis, overlays, per-agent first-help behavior, external providers, debug integration and editor integration remain open.

The cold route loads only the JSON/source/IO/digest dependencies when requested. It does not launch a compiler, a language server, a shell or a debugger. The source admission ceiling is 1 MiB; page selection is 1–8192 UTF-8 bytes and successful complete wire responses are capped at 16 KiB. Page endpoints preserve whole lines and CRLF. An oversized line requires a larger budget; it is never silently split. No latency or RSS performance result is claimed.

Snapshot identity is SHA-256 of the resolved file path plus SHA-256 of full admitted UTF-8 content. Paging rereads bounded disk content and rejects mismatched identity. This is bounded invalidation, not the planned shared immutable cache or single-flight producer. Retained historical snapshots and authenticated handles are still absent.

The host facade admits regular no-follow files; relative paths reject traversal, drive/URI syntax and controls, and ancestor checks reject current symlink directories. These checks are not an atomic sandbox against hostile ancestor replacement. The returned limitation states that boundary; SEC-01 is not fully satisfied. JSON escapes preserve source data while preventing C0 and bidi controls from changing presentation.

Normal-capability peer review: MCP diagnostics lane. Root owns final integration, generated-manual review and release admission. Lower-model sidecars: N/A; evidence-sensitive implementation and review use the assigned agents directly.
