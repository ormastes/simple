<!-- codex-design -->
# Agent Tasks — UI Access Protocol

**Feature:** `ui_access_protocol`
**Date:** 2026-04-15
**Selected Scope:** internal UI only, protocol + tools + skill, plugin packaging
**Status:** v1 shipped, including declarative observe/state parity; remaining
items are post-v1 extensions

## Agent 1: Shared UI Access Core

Own:

- `src/lib/common/ui/access.spl`
- `src/lib/common/ui/session.spl`
- `src/lib/common/ui/surface.spl`
- `src/lib/common/ui/__init__.spl`

Delivered:

- define canonical structs and IDs
- materialize snapshots from existing UI state
- record bounded recent access events
- attach persisted store support and shared window-surface registry

## Agent 2: Test API Integration

Own:

- `src/app/ui.test_api/handler.spl`
- callers in `src/app/ui.web/async_server.spl`
- callers in `src/app/ui.tui_web/server.spl`

Delivered:

- add additive `/api/test/ui/*` routes
- preserve compatibility with existing routes
- support fallback behavior when no `UISession` is present
- prefer persisted history on restart-capable runtimes

## Agent 3: MCP Tool Integration

Own:

- `src/os/services/llm/mcp_os_server.spl`
- `src/os/services/llm/tool_registry.spl`

Delivered:

- register new tools and schemas
- route window metadata through the shared runtime registry
- route actions/history/find through canonical access helpers
- keep screen/debug text derived from the same snapshot

## Agent 4: Docs, Plugin, and Skill

Own:

- `doc/01_research/.../ui_access_protocol.md`
- `doc/02_requirements/.../ui_access_protocol*.md`
- `doc/04_architecture/ui_access_protocol.md`
- `doc/05_design/ui_access_protocol*.md`
- `tools/claude-plugin/simple-ui-access/...`
- `.codex/skills/simple-ui/SKILL.md`

Delivered:

- document chosen v1 scope and rationale
- package workflow for plugin-marketplace use
- teach a single operator workflow: snapshot -> find -> observe -> state -> act
  -> history
- document persisted runtime store behavior and DB-path policy

## Agent 5: Verification

Own:

- `test/unit/app/ui/access_spec.spl`
- `test/unit/os/services/llm/tool_registry_spec.spl`

Delivered:

- validate canonical IDs, snapshots, history, persistence, and window binding
- validate tool-schema coverage
- run targeted build/test passes

## Post-v1 Extension Lanes

### Lane A: Richer declarative semantics

- expand beyond the current constrained observe/state wrappers
- keep canonical node IDs and snapshot shape unchanged

### Lane B: Vision fallback

- layer screenshot/mark helpers onto canonical surface/node references
- keep semantic protocol as the primary model

### Lane C: External accessibility adapters

- map UIA/AT-SPI/AX into the existing canonical snapshot shape
- avoid forking a second tool vocabulary
