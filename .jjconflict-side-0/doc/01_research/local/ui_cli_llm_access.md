<!-- codex-research -->
# Local Research: UI CLI LLM Access

## Goal and method

This research covers a T32-style CLI access loop for Simple UI GUI/TUI surfaces and host WM windows. Three read-only agent lanes traced the T32 CLI, common UI/WM source, and existing requirements/tests. The primary model reconciled their findings against the current source. No implementation files were changed.

## Existing contracts to reuse

The feature is largely an integration lane, not a new protocol:

- `src/lib/common/ui/access_types.spl` already defines versioned `UiAccessSnapshot`, surfaces, semantic nodes, action names, and bounded recent events. Canonical identity is `surface_id#widget_id` through `ui_access_canonical_id`.
- `src/lib/common/ui/access_snapshot.spl` builds backend-neutral snapshots from `UIState` and `UISession`; GUI and TUI share this retained state.
- `src/lib/common/ui/access_query.spl` owns in-memory find, node lookup, and JSON/text serialization.
- `src/lib/common/ui/win_text_access.spl` already normalizes TRACE32, Simple UI, host-WM, and compositor sources and centralizes find and action validation.
- `src/os/services/llm/ui_access_tools.spl`, its tool schemas/registry, and `src/app/ui.test_api/handler.spl` already expose the broader snapshot/surface/find/act/history protocol over MCP and HTTP.
- Selected requirements already exist in `doc/02_requirements/ui/ui_access_protocol.md`, `doc/02_requirements/nfr/ui_access_protocol.md`, `doc/02_requirements/app/tools/wm_text_access_mcp.md`, and `doc/02_requirements/nfr/wm_text_access_mcp.md`. New requirements must extend rather than fork them.

The higher reusable rung is therefore `common.ui.access` plus `common.ui.win_text_access`; creating a second `UiCliAccess` data model would duplicate selected behavior.

## T32 precedent

The standalone entrypoint is `examples/10_tooling/trace32_tools/t32_cli/mod.spl:t32_cli_main` (also exposed through source symlinks under `src/app`). `commands.spl:T32CliCommand/all_cli_commands` maps 36 CLI commands to MCP tools. Relevant commands include:

- `windows` for the catalog;
- `window show`, `window open`, and `window describe` for capture and metadata;
- action and field commands;
- `history`, status, resource, dialog, and job commands.

`bridge.spl` delegates to the T32 MCP owners, `types.spl` defines structured bridge results, and `render.spl` owns deterministic human formatting. `session_tools.spl` blocks known GUI/script-hanging commands unless explicitly forced. Catalog loading, identifier validation, shell validation, central error codes, and capture fallback fail loudly.

Important distinction: the repository's `windows` command lists configured capability/catalog records, not necessarily every currently open OS window. Real live TRACE32 window discovery is a separate adapter concern.

Tests already protect registry/parity/render/error behavior under `test/01_unit/app/t32_cli/`, with live scenarios under `test/02_integration/t32_hw/`.

## Current CLI gaps

- `src/app/ui/cli_entry.spl` is the deployed narrow `simple ui` entrypoint. It runs render backends but does not dispatch snapshot/surface/find/act/history or the existing `ui cli` observer.
- `src/app/ui.cli/observer.spl` observes a local `.ui.sdn` state and exposes `state`, `changes`, `tree`, `watch`, and `adaptive`; it is not the live semantic access protocol.
- `src/app/play/main.spl` advertises `wm-list` and `wm-text-snapshot|find|act`, but currently returns planned command output rather than invoking live WM/common access adapters.
- `src/lib/nogc_sync_mut/play/wm/mod.spl` already provides live cross-platform window listing and host actions through `WindowInfo`.
- `common.ui.win_text_access` imports that mutable play/backend `WindowInfo`, creating an upward dependency in the supposed common core. The smallest correction is adapter-owned conversion into common UI records; moving a minimal descriptor down is the fallback if multiple adapters need it.
- Common action routing validates a semantic route but does not itself execute backend actions, refresh state, and record correlated history. One adapter execution boundary is missing.
- Current UI snapshot construction can leave `action_names` empty; actions must come from owner metadata rather than renderer inference.

No language/compiler change is indicated. Command routing and native entry-closure builds may need updates because the Rust driver maps `ui` to the narrow entry and the pure-Simple command table is not symmetrical.

## Existing design and evidence

`doc/05_design/ui/access/ui_access_protocol_tui.md` already sketches `simple ui snapshot|find|act|history`, human output by default, and structured output for machines. `doc/04_architecture/lib/wm_text_access_mcp.md` and `doc/05_design/lib/web/wm_text_access_mcp.md` define the adapter envelope over the common access core.

Focused evidence should extend:

- `test/01_unit/app/ui/access_spec.spl` and `ui_access_store_spec.spl`;
- `test/01_unit/os/services/llm/ui_access_dispatch_spec.spl`;
- `test/03_system/app/os/feature/ui_access_protocol_spec.spl`;
- `test/03_system/app/wm_text_access_mcp/feature/wm_text_access_mcp_spec.spl`;
- `test/05_perf/ui_access/ui_access_hot_paths_spec.spl`;
- T32 list/capture/parity specs for reference behavior.

Several WM system checks currently assert source strings rather than live command behavior. The new system lane must execute the CLI adapters and verify schema, errors, actions, refresh, and history.

## Smallest coherent implementation direction

1. Reuse the existing UI access types, query, serializer, event store, and WinText normalization.
2. Add a thin live CLI dispatcher to the deployed `simple ui` entry, using the same protocol operations already exposed by MCP/HTTP.
3. Turn existing `simple play wm-list|wm-text-*` planning commands into live adapter calls; add only the minimum compatible spelling needed for symmetric window listing.
4. Keep live enumeration/capture/action in source adapters and all normalization/query/serialization/error policy in common owners.
5. Add generation/revision-aware stale-target checking before action, then refresh and record correlated result history.
6. Preserve existing commands and routes; make additions additive.

## Cooperative review result

The T32, common UI/WM, and docs/tests lanes agreed that a new parallel model is unnecessary. The primary/highest-capability review accepts the research only with these corrections: treat T32 names as non-unique, distinguish catalog from live windows, do not infer actions, and do not claim the current planned WM CLI is live.

