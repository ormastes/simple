# Source-view foundations and native structural projection

<!-- codex-architecture -->

Status: authored on isolated release worktrees; runtime admission and full-plan acceptance remain open. The full selected plan is retained under `doc/03_plan/release/1.0.0/inputs_2026-11-06/`.

Common source contracts own byte ranges, snapshot/projection/session/outline values. `nogc_sync_mut/source/projection.spl` preserves exact selected bytes and omissions; `structure.spl` consumes provider nodes, orders them with stable merge sort and selects folded outline or focused syntax. Neither layer imports a compiler or implements a competing grammar.

`compiler/90.tools/source_outline_v1.spl` adapts the existing native token parser with heuristic mode disabled. It reports L1 syntax candidates, not semantics; function bodies are not typechecked. The canonical outline owner repairs inline body skipping and fully initializes newer module fields. Native source is capped at 64 KiB and 512 nodes before view construction; parser errors remain visible as partial syntax. SDN/SHS exact structural providers remain unavailable pending their canonical span/dialect owners.

`app/source_view/service.spl` publicly composes IO, native provider and projection. Its typed SourceOpenResultV1 carries source-contract JSON and is_error, without a transport envelope. MCP and Caret HTTP are thin adapters. Native provider imports are request-local; raw reads and startup/tool discovery do not instantiate a native parser or launch a compiler, server, shell or debugger. No cold/warm timing or RSS result is claimed.

Unbound MCP exposes its lack of authenticated logical-agent isolation. The separate authenticated host supplies session state and owns serialized first-help commit. It must bind its configured workspace to the actual canonical process root and enforce live registry/capability checks; arbitrary body IDs are never authentication. Bound rendering applies display labels without modifying exact source; inline-information/hint providers remain unavailable.

Raw admission is 1 MiB, raw/source page budget 1–8192 bytes, shared successful payload 12 KiB, and MCP complete response 16 KiB. RPC IDs are valid JSON-RPC scalar kinds capped at 128 bytes; invalid/oversized IDs receive a bounded null-ID protocol error. HTTP must enforce its own complete envelope cap before committing first-help.

Snapshots bind canonical path and full UTF-8 content using SHA-256. Structural cursors additionally bind mode, target, depth and budgets. Disk rereads and native reparsing are bounded but are not the planned shared immutable cache. Preserved omissions, parse issues and explicit partial-context state prevent a bounded view from claiming exhaustive analysis.

Imports use ordered noncontiguous range sets; no intervening source is included in a fabricated contiguous import span. More than 64 import ranges requires explicit bounded raw expansion; large outlines paginate. Focus resolves unique syntax names/qualified methods, opens the target and parent context, folds siblings and rejects ambiguity. Relevant-import semantic selection remains not evaluated.

The canonical IO facade checks regular no-follow files and existing non-symlink ancestors. This is not atomic root-relative confinement against hostile ancestor replacement. The limitation remains explicit and SEC-01 remains open. JSON presentation escapes C0 and bidi controls reversibly.

Review/integration: root; authentication: mcp_lsp_audit. Peer static review and runtime/manual evidence are separate. No full-plan completion follows from this incremental implementation.

Bound service calls carry the authenticated owner's explicit canonical `workspace_root`; they do not reread process cwd after authorization. The unbound local MCP path captures cwd once. Descriptor-relative protection against malicious directory replacement remains a separate open IO requirement.

Pagination now carries charged, deduplicated enclosing headers on every page; missing budget yields an explicit mandatory-context error. Cursor identity additionally binds canonical produced-outline content, while true provider-build provenance stays explicitly unavailable.
