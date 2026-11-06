<!-- codex-design -->
# Release 1.0.0 memory and MCP/LSP detail design

Status: **OPEN**. [Architecture](../04_architecture/release100_memory_mcp_lsp.md) and [requirements](../02_requirements/feature/release100_memory_mcp_lsp.md) incorporate both full selected plans. Detailed source-view examples, TUI/debug screen, source contracts, stage models, ownership state transitions, transaction steps and error semantics remain as specified there; this integration design does not replace them with smaller semantics.

## State and identity

Use the existing normative ownership states uninitialized/live/moved/dropped plus projected-place initialization, CFG joins and short-borrow effect facts. The source/HIR semantic policy authority decides whether mandatory checking applies; textual source searches or unrelated diagnostic flags cannot authorize bypass. Required cleanup comes from live-on-exit facts with initialized-member order and fallible transfer commit semantics.

Shared source records carry immutable snapshot identity, exact original/decoded byte spans and explicit position encodings. Source segments and virtual annotation segments are distinct. A view carries capabilities/completeness, omission ranges/reasons and resolvable continuation handles. A session carries authenticated principal/workspace/logical-agent binding, generation, preference version, request-id deduplication, help version, current view and navigation/fold state. Defaults are numbers off, important inline information, hints off and ASCII decoration; original Unicode source is preserved.

First-help state changes only after successful view production, atomically with the versioned result. Concurrent first opens emit it once. Retried preference requests set a desired value rather than repeating a toggle; conflict/expiry results are explicit. Reconnect requires authorized logical-session binding. A session identifier alone is not authorization, and a transport connection alone is not a subagent identity.

## Algorithms and error paths

1. Resolve the authorized workspace/document/overlay and immutable version, distinguishing a valid empty file from read failure.
2. Select an available native/structural/semantic provider with explicit evidence level and environment identity; passive reads do not execute source or workspace commands.
3. Select raw/outline/focused source ranges before serialization. Preserve source tokens and ordering; noncontiguous groups retain range sets. Bound traversal and keep coherent evidence units.
4. Attach only available diagnostic/semantic/history/debug facts, preserving warning severity, related labels, structured locations and failure/pending/stale states. Analyzer failure must not become clean/unchanged/zero errors.
5. Render ASCII/Unicode decoration separately from source; record every omission and partial context. Editor/protocol positions convert through the shared map, never through rendered display columns.
6. Apply session changes atomically, then return bounded protocol output with no diagnostic stdout contamination. Cancellation releases request resources without poisoning shared work.

Fix application follows source-plan §16: resolve/preview, validate exact versions and permissions, detect overlaps, coordinate editor or filesystem ownership, publish through existing transaction owners, retain receipts and reanalyze honestly. Empty replacement means deletion. Multi-file partial application cannot be reported as full success. Undo checks successor versions. Debug replacement remains a separate admitted operation.

## Interface freeze and parallel sequencing

Existing contracts take precedence over invented aliases. Root and source_view froze V1 types `SourceSnapshotV1`, `SourceRangeV1`, `SourceSelectionV1`, `SourceProjectionV1`, `SourceViewPreferencesV1` and functions `source_view_session_new_v1`, `source_view_set_preferences_v1`, `source_view_commit_open_v1`, `source_project_ranges_v1`, `source_project_raw_v1` before consumer wiring. The adapter is `main_lazy_source_tools.spl`, integrated through `main_dispatch.spl`, `tool_table.spl` and `main_static_tools.spl`. Raw/range foundation behavior does not imply per-method folded outline, complete session authentication or semantic-provider support; each remains open until its actual front-door tests pass. Conceptual boundaries are SourceSnapshotStore, SourceAnalysisService/QueryPlanner, SourceProjectionService, ViewSession and existing DebugServiceV1; names in the selected plan are not evidence that a corresponding physical module exists.

The initial independent edits are strict no-GC driver gating and MCP diagnostic compatibility handling. Source-view foundations own new shared modules/tests and the identified adapter; debug_truth independently removes fabricated successful answers in debug tools while real shared-target capabilities remain open. Root resolves integration, reviews source maps and runtime failure paths, and requires public-interface evidence before advertising a capability.

## UI and knowledge continuity

The retained MCP plan §§7–9 and §12.2 supplies the selected outline/focused/raw, compact help, annotation and debugger-screen layouts. Rendering must be verified with text/GUI captures and exact source maps, including narrow terminals; no screenshot/mockup alone proves behavior. Preserve legacy reader profiles and explicit raw access during migration.

Each implemented slice updates its owning guide, mirrored manual and feature/layer expert wiki, plus relevant bug records and tooling workflow instructions. These deliverables are open until the implementation owner lists concrete paths and root reviews them. New test helper placeholders must fail explicitly; no no-op helper or source-text presence assertion can discharge a runtime requirement.
