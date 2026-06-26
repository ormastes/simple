<!-- codex-plan -->
# Agent Task Plan: KAIROS-Like Simple MCP + LLM Dashboard

Date: 2026-06-25

## Scope

Selected requirement set: `doc/02_requirements/app/dashboard/kairos_like_simple_mcp_llm_dashboard.md`.

This lane covers the assistant core, dashboard replay/import, live bridge
projection, operator visibility, and structured failure evidence surfaces.
It does not include vLLM/Torch runtime implementation; that remains gated by
`doc/03_plan/agent_tasks/llm_runtime_vllm_torch_interface.md`.

## Current Slices

### Slice A: Agent Dashboard Hardening

- Owner: Codex main lane
- Sidecar: Spark review completed for absence/slot/render risks
- Normal reviewer: completed; display-label absence leak fixed
- Files:
  - `src/app/llm_dashboard/data/agent_tree.spl`
  - `src/app/llm_dashboard/data/agent_position.spl`
  - `src/app/llm_dashboard/tui/agent_panel.spl`
  - `src/app/llm_dashboard/tui/agent_sprites.spl`
- Evidence:
  - `test/01_unit/app/llm_dashboard/agent_dashboard_hardening_spec.spl`
  - `test/unit/app/llm_dashboard/agent_dashboard_hardening_spec.spl`
  - 2026-06-26 public manual hardening: both mirrored agent hardening specs
    pass 44/44, the generated manuals were refreshed/synced, and public
    snippets no longer expose raw absence checks, boolean negative-containment
    wrappers, or the internal absence marker.

### Slice B: Dashboard Replay Collector and Live Bridge Projection

- Owner: Codex main lane
- Sidecar: N/A for initial patch; normal review completed and blockers fixed
- Files:
  - `src/app/dashboard/assistant_collectors.spl`
  - `src/app/dashboard/assistant_bridge.spl`
  - `src/app/dashboard/assistant_live_view.spl`
  - `src/app/dashboard/assistant_import.spl`
  - `src/app/dashboard/assistant_digest.spl`
  - `src/app/dashboard/__init__.spl`
  - `src/app/llm_dashboard/data/jsonl_watcher.spl`
- Evidence:
  - `test/01_unit/app/llm_dashboard/assistant_collectors_spec.spl`
  - `test/unit/app/llm_dashboard/assistant_collectors_spec.spl`
  - `test/01_unit/app/llm_dashboard/assistant_bridge_spec.spl`
  - `test/unit/app/llm_dashboard/assistant_bridge_spec.spl`
  - `test/01_unit/app/llm_dashboard/assistant_live_view_spec.spl`
  - `test/unit/app/llm_dashboard/assistant_live_view_spec.spl`
  - `test/01_unit/app/llm_dashboard/assistant_import_spec.spl`
  - `test/unit/app/llm_dashboard/assistant_import_spec.spl`
  - `test/01_unit/app/llm_dashboard/assistant_digest_spec.spl`
  - `test/unit/app/llm_dashboard/assistant_digest_spec.spl`
  - `test/01_unit/app/llm_dashboard/jsonl_watcher_spec.spl`
  - `test/unit/app/llm_dashboard/jsonl_watcher_spec.spl`

## Remaining Work

1. MCP assistant store API hardening:
   - Root-facing store APIs now accept parsed JSON tool input.
   - Root-facing `any` APIs reject non-object parsed values instead of routing
     malformed input into typed serializers.
   - Typed session creation generates a session ID when a valid session object
     omits one, avoiding `.json` key collisions.
   - Typed internal callers route through record-specific store functions.
   - State updates increment persisted event metadata before writing the
     session summary back to disk.
   - `test/01_unit/app/mcp/assistant/session_store_spec.spl` and mirrored
     `test/unit/app/mcp/assistant/session_store_spec.spl` pass.
   - `test/01_unit/app/mcp/assistant/session_views_spec.spl` and mirrored
     `test/unit/app/mcp/assistant/session_views_spec.spl` pass after fixing
     timeline count inflation and numeric brief rendering.
   - Parsed JSON events with `"kind":"signal"` are normalized to persisted
     `"signal_event"` while preserving `signal`/wake reason fields; store and
     view specs cover this path.
2. MCP assistant control surface:
   - Start/spawn/pause/resume/brief/list/timeline/signal/task tools are
     exposed through MCP with `in_process` handlers.
   - `src/app/mcp/main_lazy_assistant.spl` uses explicit optional-session
     matching for store readback so handler output never dereferences an
     unresolved optional value.
   - `src/app/dashboard/assistant_collectors.spl` exports
     `collect_assistant_timeline` for dashboard e2e readback of persisted MCP
     assistant timelines.
   - Dashboard collectors use `assistant_store_load_session` so snapshots see
     the same timeline-merged session metadata as MCP views.
   - Signal push fails the MCP call if the timeline event cannot be persisted.
     Status: done on 2026-06-26; `handle_assistant_push_signal` now checks the
     `assistant_store_append_event_record` result before state update, and the
     dashboard e2e spec proves a pushed `wake` signal is persisted as
     `signal_event` and visible through `collect_assistant_timeline`.
   - Evidence:
     - `test/01_unit/app/mcp_unit/assistant_surface_spec.spl` passes with 3/3.
     - `test/unit/app/mcp_unit/assistant_surface_spec.spl` passes with 3/3.
     - `test/01_unit/app/mcp_unit/assistant_task_linking_spec.spl` passes.
     - `test/unit/app/mcp_unit/assistant_task_linking_spec.spl` passes.
     - `test/01_unit/app/mcp_unit/assistant_dashboard_e2e_spec.spl` and
       mirrored `test/unit/app/mcp_unit/assistant_dashboard_e2e_spec.spl` pass
       with 1/1, including persisted MCP signal readback in the dashboard
       timeline and without internal process-exit diagnostics after narrowing
       fixture file operations to `std.io_runtime`.
3. Dashboard live mode:
   - `src/app/dashboard/assistant_live_view.spl` connects replay snapshots to
     bridge projections and renders absence-safe dashboard state lines.
   - Fresh live snapshots enable operator controls routed to `assistant_core`.
   - Replay, stale, and degraded snapshots remain read-only with operator
     notices explaining refresh or replay constraints.
   - `src/app/web_dashboard/server.spl` now serves authenticated `/agents`
     requests through the assistant snapshot collector and live-view renderer,
     redirects unauthenticated or blank-session `/agents` requests to `/login`,
     matches only `/agents` and `/agents/...` rather than unrelated prefixes,
     and keeps the dashboard shell linked to `/agents`.
   - Evidence:
     - `test/01_unit/app/llm_dashboard/assistant_live_view_spec.spl` passes.
     - `test/unit/app/llm_dashboard/assistant_live_view_spec.spl` passes.
     - `test/03_system/feature/app/web_dashboard/llm_agent_dashboard_spec.spl`
       passes with authenticated `/agents` readback, blank-session redirect,
       absence-safe output, and shell link coverage.
     - 2026-06-26 public manual hardening: the `/agents` system spec now uses
       helper/count-based absence assertions, and both generated manuals were
       refreshed so public expected-code snippets do not expose the internal
       absence marker.
     - `test/03_system/feature/app/web_dashboard/web_dashboard_server_spec.spl`
       passes after updating stale login-module source contracts to the current
       minimal router/auth behavior.
4. Replay/import mode:
   - `src/app/dashboard/assistant_import.spl` imports JSON snapshot exports
     into a chosen durable replay root using the assistant store layout.
   - Imported sessions, timeline events, and notifications are readable through
     `collect_assistant_snapshot_from_root`.
   - Snapshot imports require `sessions`, `timeline`, and `notifications`
     arrays up front; missing or malformed required arrays return structured
     errors before any replay streams are written.
   - Imported child task metadata, child session IDs, tool-use IDs, and warnings
     are preserved for task-tree replay.
   - Repeat imports replace per-session timeline/notification snapshot streams
     instead of duplicating events.
   - Malformed payloads return structured import errors without creating a
     replay snapshot.
   - Evidence:
     - `test/01_unit/app/llm_dashboard/assistant_import_spec.spl` passes.
     - `test/unit/app/llm_dashboard/assistant_import_spec.spl` passes.
5. Failure evidence:
   - `src/app/dashboard/assistant_live_view.spl` renders explicit failure
     state, detail, and count fields for assistant crashes, missing selected
     sessions, stale bridge snapshots, and degraded bridge snapshots.
   - Failure evidence remains absence-safe in rendered dashboard lines.
   - Evidence:
     - `test/01_unit/app/llm_dashboard/assistant_live_view_spec.spl` covers
       failed session/crash metadata, missing selected-session evidence, and
       stale bridge evidence.
     - `test/unit/app/llm_dashboard/assistant_live_view_spec.spl` mirrors the
       same coverage.
6. Retention/backpressure:
   - `src/app/dashboard/assistant_retention.spl` adds dashboard-facing
     bounded timeline/notification retention projection.
   - The projection tails visible events, coalesces repeated signal and
     notification bursts, reports dropped/coalesced counts, and emits a
     absence-safe `normal`/`backpressure` notice for operators.
   - Evidence:
     - `test/01_unit/app/llm_dashboard/assistant_retention_spec.spl` passes.
     - `test/unit/app/llm_dashboard/assistant_retention_spec.spl` passes.
   - `src/app/mcp/assistant/session_store_part2.spl` now adds
     `assistant_store_prune_session_retention(...)`, a durable store-level
     retention pass that rewrites timeline and notification JSONL files to
     bounded tails, reports retained/dropped counts, and preserves the current
     digest checkpoint id.
   - Evidence:
     - `test/01_unit/app/mcp/assistant/session_store_spec.spl` proves persisted
       JSONL tails are actually pruned on disk and the digest checkpoint id is
       preserved.
     - `test/unit/app/mcp/assistant/session_store_spec.spl` mirrors the same
       durable retention coverage.
   - Store digest policy now writes digest checkpoints to per-session JSONL,
     updates the selected session checkpoint id, and prunes old digest
     checkpoints to a bounded tail.
   - Evidence:
     - `test/01_unit/app/mcp/assistant/session_store_spec.spl` proves durable
       digest generation, current-checkpoint update, and old-checkpoint pruning.
     - `test/unit/app/mcp/assistant/session_store_spec.spl` mirrors the same
       digest checkpoint coverage.
7. Digest/brief replay readback:
   - `src/app/dashboard/assistant_digest.spl` projects digest-style dashboard
     readback from persisted snapshot fields: session summary, digest checkpoint
     ID, latest event detail, task result-summary count, warnings, and
     notifications.
   - The projection renders option-like absence (`none`/`missing`) and remains
     absence-safe for missing selected sessions.
   - Evidence:
     - `test/01_unit/app/llm_dashboard/assistant_digest_spec.spl` passes.
     - `test/unit/app/llm_dashboard/assistant_digest_spec.spl` passes.
   - MCP store digest generation and durable multi-checkpoint pruning are
     covered by the session-store digest checkpoint scenario.
8. Transcript JSONL watcher:
   - `src/app/llm_dashboard/data/jsonl_watcher.spl` tails project transcript
     `.jsonl` files for dashboard ingestion.
   - Newly discovered transcripts start at EOF so the dashboard does not replay
     old backlog, appended lines are returned on later polls, truncation resets
     offsets for rotated files, incomplete trailing JSONL records are held
     until newline termination, and stray files in the root are ignored.
   - Specs use narrow `std.io_runtime` fixture helpers rather than broad
     `app.io.mod` compatibility imports.
   - Evidence:
     - `test/01_unit/app/llm_dashboard/jsonl_watcher_spec.spl` passes.
     - `test/unit/app/llm_dashboard/jsonl_watcher_spec.spl` passes.
9. vLLM runtime evidence panel:
   - `src/app/llm_dashboard/collectors/diagnostics_jsonl_collector.spl`
     recognizes `llm_runtime_vllm_*` JSONL evidence from the runtime lane and
     surfaces `vllm_events`, latest status, and latest reason in the existing
     diagnostics text/HTML panels.
   - Missing vLLM evidence renders as `none`; HTML escapes status/reason fields
     and public output remains absence-marker-free.
   - Evidence:
     - `test/01_unit/app/llm_dashboard/collectors/diagnostics_jsonl_collector_spec.spl`
       passes with vLLM evidence count/status/reason coverage.
     - `test/unit/app/llm_dashboard/collectors/diagnostics_jsonl_collector_spec.spl`
       mirrors the same coverage.
10. vLLM dashboard control panel:
   - `src/app/llm_dashboard/collectors/vllm_control_panel.spl` adds a
     dashboard-facing operator control panel for vLLM `preflight`, `start`,
     `poll`, `probe`, and `stop` intents.
   - The panel validates manifest/action/pid inputs, emits
     `llm_dashboard_vllm_control_panel` JSONL, renders text/HTML controls, and
     is embedded in `src/app/web_dashboard/server.spl`.
   - The web route `/api/vllm/control` returns authenticated JSONL action
     evidence. This slice is intentionally action-intent only: live process
     execution remains owned by `app.llm_runtime` lifecycle/readiness facades so
     importing the dashboard does not load HTTP/process backends.
   - The route now accepts query-style `base_model`/`base-model`, `endpoint`,
     `vllm_available`/`vllm-available`, and
     `gpu_available`/`gpu-available` overrides, matching the runtime control
     command's dashboard-friendly argument shape while preserving the
     intent-only dashboard boundary.
   - Evidence:
     - `test/01_unit/app/llm_dashboard/collectors/vllm_control_panel_spec.spl`
       passes.
     - `test/unit/app/llm_dashboard/collectors/vllm_control_panel_spec.spl`
       mirrors the same coverage.
     - `test/01_unit/app/llm_dashboard/ios_mode_spec.spl` and mirrored
       `test/unit/app/llm_dashboard/ios_mode_spec.spl` pass after preserving the
       existing dashboard server constructor surface.
     - `test/03_system/feature/app/web_dashboard/vllm_control_route_spec.spl`
       passes and proves authenticated `/api/vllm/control` JSONL readback,
       query-style overrides, missing-resource skipped evidence, redaction,
       dashboard HTML embedding, and the dashboard-safe collector boundary.

## Open Bugs Found During This Lane

- Resolved: dashboard collector/e2e specs previously printed an internal
  `Process exited with code 1` diagnostic after passing assertions because
  fixture cleanup imported broad `app.io.mod` surfaces. The specs now use
  `std.io_runtime` file helpers and pass cleanly.
- Signal event append previously hung under SSpec when persisted as literal
  kind `"signal"`; the store now persists `signal_event` and keeps the wake
  reason in the `signal` field.
- Resolved: normal review found snapshot import discarded task-tree fields and
  appended duplicate stream events on repeat import. Import now preserves
  `children`, `tool_use_ids`, `warnings`, and `child_tasks`, and replaces
  per-session timeline/notification JSONL streams for imported snapshots.
- Resolved: normal review found retention dropped counts double-counted
  coalesced events. Dropped counters now track retention overflow only, while
  coalesced counters report burst collapse separately.
- Resolved: normal review found partial transcript JSONL records could be
  emitted before newline termination and then lost. The watcher now advances
  offsets only through complete newline-terminated records.
- Resolved: normal review found malformed snapshot imports with missing
  required arrays could pass as zero-count imports. Import validation now
  rejects missing `sessions`, `timeline`, or `notifications` arrays before
  writing replay data.

## Merge Owner and Final Reviewer

- Merge owner: Codex main lane
- Final reviewer: normal/high-capability LLM review after all selected
  dashboard requirements have executable evidence
