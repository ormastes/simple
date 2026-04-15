<!-- codex-design -->
# Agent Tasks — UI Access Protocol

**Feature:** `ui_access_protocol`
**Date:** 2026-04-15
**Selected Scope:** internal UI only, protocol + tools + skill, plugin packaging
**Status:** v1 shipped, including declarative observe/state parity plus
structured query parity; remaining items are post-v1 extensions

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
- expose structured JSON query results without changing legacy find/observe
  compatibility
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

## Concrete Next-Wave Interface

The next wave should keep the existing canonical snapshot shape as the stable
center and add only additive interfaces around it.

### Shared contract additions

- value semantics:
  - `ui_access_value` tool/route
  - canonical selector inputs: `surface_id`, `canonical_id`, `kind`, `text`,
    `focused_only`
  - value inputs: `value_key`, `value`, `clear_first`
  - read result shape: `query`, `match_count`, `nodes`, `value_key`, `values`
- vision fallback:
  - `ui_access_marks` and `ui_access_describe_point` as separate additive reads
  - mark output must carry `surface_id`, `canonical_id?`, `mark_id`,
    `bbox`, `label`, `source`
- external adapters:
  - adapter-backed snapshot ingestion must target the same canonical
    `UiAccessSnapshot` shape
  - adapter metadata should be additive fields, not a second node model
- perf verification:
  - one repo-native perf smoke harness covering snapshot, query, and ensure
  - one NFR section with startup/query/ensure budgets

### Lane A: Richer declarative semantics

Own:

- `src/lib/common/ui/access.spl`
- `src/os/services/llm/mcp_os_server.spl`
- `src/app/ui.test_api/handler.spl`
- `src/os/services/llm/tool_registry.spl`
- focused unit/system/MCP specs for `ui_access_*`

Start with:

- concrete additive `ui_access_value` read/write semantics
- value reads over canonical selectors
- the smallest truthful write path for text-capable nodes

Rule:

- keep canonical node IDs and snapshot shape unchanged
- do not overload `ui_access_state` with typed value semantics
- keep `value` truth tied to live snapshot state, not guessed history

### Lane B: Vision fallback

Own:

- new additive files under `src/lib/common/ui/vision*`
- new HTTP/MCP read-only routes/tools for marks/describe-point
- vision-specific tests and docs only

Start with:

- mark generation and point description over existing surfaces
- explicit `source` metadata so agents can tell semantic vs visual outputs apart

Rule:

- semantic protocol stays primary
- vision results must reference canonical surface/node ids when known
- no replacement of `snapshot/query/ensure`

### Lane C: External accessibility adapters

Own:

- new additive adapter modules under `src/lib/common/ui/adapters*`
- adapter research/docs
- adapter-backed integration tests

Start with:

- one adapter registry/interface
- one synthetic/internal adapter implementation used for testing the contract
- one external adapter behind an explicit opt-in, after the contract is stable

Rule:

- map UIA/AT-SPI/AX into the existing canonical snapshot shape
- avoid forking a second tool vocabulary
- keep native handle metadata runtime-only unless proven stable

### Lane D: Perf verification

Own:

- `test/perf/ui_access_*`
- NFR and system-test planning docs

Start with:

- snapshot/query/ensure perf smoke on representative fixtures
- deterministic budgets recorded in docs and checked in CI-friendly form
