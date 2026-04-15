<!-- codex-design -->
# Agent Tasks — UI Access Protocol

**Feature:** `ui_access_protocol`
**Date:** 2026-04-15
**Selected Scope:** internal UI only, protocol + tools + skill, plugin packaging

## Agent 1: Shared UI Access Core

Own:

- `src/lib/common/ui/access.spl`
- `src/lib/common/ui/session.spl`
- `src/lib/common/ui/surface.spl`
- `src/lib/common/ui/__init__.spl`

Tasks:

- define canonical structs and IDs
- materialize snapshots from existing UI state
- record bounded recent access events
- keep surface-aware history cheap and readable

## Agent 2: Test API Integration

Own:

- `src/app/ui.test_api/handler.spl`
- callers in `src/app/ui.web/async_server.spl`
- callers in `src/app/ui.tui_web/server.spl`

Tasks:

- add additive `/api/test/ui/*` routes
- preserve compatibility with existing routes
- support fallback behavior when no `UISession` is present

## Agent 3: MCP Tool Integration

Own:

- `src/os/services/llm/mcp_os_server.spl`
- `src/os/services/llm/tool_registry.spl`

Tasks:

- register new tools and schemas
- overlay window metadata onto access surfaces
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

Tasks:

- document chosen v1 scope and rationale
- package workflow for plugin-marketplace use
- teach a single operator workflow: snapshot -> find -> act -> history

## Agent 5: Verification

Own:

- `test/unit/app/ui/access_spec.spl`
- `test/unit/os/services/llm/tool_registry_spec.spl`

Tasks:

- validate canonical IDs, snapshots, and history
- validate tool-schema coverage
- run targeted and broader build/test passes
