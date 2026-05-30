# IDE + LLM / Agent-Dashboard Integration Guide

How the Simple **IDE/editor** surfaces connect to the **LLM agent dashboard**
and **assistant session manager**. This guide is descriptive of what exists in
the tree today — each claim is grounded in a file/symbol, and the
"wired vs. contract-only" status is called out explicitly so nobody mistakes a
designed seam for a running one.

Architecture background (read-only, pipeline-owned):
`doc/04_architecture/kairos_like_simple_mcp_llm_dashboard.md` and
`doc/05_design/kairos_like_simple_mcp_llm_dashboard.md` (KAIROS three-plane
model). Editor surface details: `doc/07_guide/editor_tui.md`.

## The pieces

### IDE / editor surfaces

| Surface | Path | Launch | Notes |
|---|---|---|---|
| **svim** (vim-like TUI) | `src/app/svim/` | `bin/simple run src/app/svim/main.spl <files> [--interactive]` | Line/TUI editor over the shared session model |
| **Editor TUI** | `src/app/editor/tui_main.spl` | `bin/simple run src/app/editor/tui_main.spl <files>` | Split-pane, file-tree, diagnostics, command palette (`EditorController`) |
| **Editor GUI** | `src/app/editor/gui_shell_core.spl` | GUI shell (SDL/Winit) | Same backend, desktop shell |
| **Simple IDE** | `src/app/ide/main.spl` | `bin/simple run src/app/ide/main.spl [--tui|--gui|--gui-sdl] <files>` | Thin VS Code-like product entrypoint over the shared editor launch contract |
| **Example IDE** | `examples/ide/simple_ide_launch.spl` | `bin/simple run examples/ide/simple_ide_launch.spl` | Minimal embedded/sample IDE launch integration |
| **Shared backend** | `src/lib/editor/` (~129 files) | — | Piece-table buffers, multi-buffer, split panes, LSP/diagnostics/markdown/wiki services |

Both svim and the Editor consume the same `src/lib/editor/` backend (epic
`.spipe/editor-ide-platform`, CLOSED 2026-05-20).

The reusable backend uses semantic package names (`buffer`, `core`, `view`,
`render`, `extensions`, `services`, `unified`) rather than duplicate numbered
layer directories. MDSOC+ layer boundaries are still part of the architecture,
but code paths stay VS Code-like so TUI, GUI, embedded editor apps, examples,
and the VS Code extension all point at one library surface.

Launch-mode parsing is also shared: `src/lib/editor/core/launch.spl` owns the
pure `EditorLaunchOptions` contract used by `src/app/editor/main.spl`,
`src/app/editor/tui_main.spl`, `src/app/ide/main.spl`, and
`examples/ide/simple_ide_launch.spl`.
Reusable path/text helpers are shared through `src/lib/editor/core/path_text.spl`
so editor controllers and MCP helpers do not keep separate dirname, basename,
payload, CSV, integer, and markdown-path parsers.
Extension-root policy is shared through `src/lib/editor/extensions/roots.spl`;
the app adapter injects `SIMPLE_EDITOR_EXTENSION_PATH` and `HOME` so host
environment access stays out of the reusable library policy.

### Host and SimpleOS runtime contract

The IDE must run on both host platforms and SimpleOS:

- **Shared logic:** `src/lib/editor/` stays runtime-neutral. It owns buffers,
  documents, views, markdown-first services, LSP/DAP models, extension metadata,
  and unified adapters.
- **SimpleOS path:** `src/app/editor/tui_main.spl`,
  `src/app/editor/tui_shell.spl`, and `src/lib/editor/70.backend/tui_backend.spl`
  use terminal/TUI abstractions only and must not import Tauri, Electron,
  browser/webview, SDL, or desktop dialog/clipboard APIs.
- **Host path:** GUI, SDL, browser, Tauri, and desktop affordances remain in
  host adapters such as `src/app/editor/gui_shell_*`,
  `src/app/editor/desktop_commands.spl`, `src/app/ui.tauri/`, and
  `src/app/ui.browser/`.
- **Portable GUI render:** `src/lib/editor/70.backend/gui_backend.spl` renders
  editor and markdown surfaces to pure HTML strings. Host web/Tauri shells own
  presentation and IPC, but the editor/IDE renderer itself stays runnable
  without host-only APIs.
- **Verification:** `test/unit/lib/editor/host_simpleos_surface_contract_spec.spl`
  guards the boundary by scanning the shared/TUI entrypoints for host-only API
  names and by rendering editor GUI HTML through the shared GUI backend.

### LLM session management

| Piece | Path | Role |
|---|---|---|
| **Assistant session store** | `src/app/mcp/main_lazy_assistant.spl` + assistant store module | File-backed sessions/timelines/notifications/child-tasks; **source of truth** |
| **Assistant MCP tools (11)** | routed in `src/app/mcp/main_dispatch.spl` | `assistant_start`, `assistant_spawn_task`, `assistant_pause`, `assistant_resume`, `assistant_brief`, `assistant_list_sessions`, `assistant_get_session`, `assistant_get_timeline`, `assistant_push_signal`, `assistant_list_tasks`, `assistant_get_notifications` |
| **Agent dashboard** | `src/app/llm_dashboard/` | `simple dashboard agents` → `run_llm_dashboard`; TUI + web views of agent tree, activity feed, tasks, provider status |
| **Dashboard assistant views** | `src/app/dashboard.views/assistant_*.spl` | Render session status / timeline / tasks / overview |
| **Dashboard bridge** | `src/app/dashboard/assistant_bridge.spl` | Attach-to-snapshot policy (live / stale / degraded); observer, never source-of-truth |

### Shared store (the integration backbone)

```
.build/llm_dashboard/assistant/
  sessions/        # session records (JSON)
  timelines/       # appended timeline events (JSONL)
  notifications/   # appended notifications (JSONL)
```
`ASSIST_ROOT = ".build/llm_dashboard/assistant"` in `main_lazy_assistant.spl`.
The assistant tools **write**; the dashboard views + bridge **read** the same
files. This file-backed store is the actual coupling between the LLM-control
plane (MCP assistant) and the operator plane (dashboard).

## How it fits together (KAIROS three-plane)

```
  Editor / IDE                MCP server (`simple mcp`)            Dashboard
  ┌────────────┐   editor.*   ┌───────────────────────┐         ┌──────────────┐
  │ svim /     │  (in-proc,   │ assistant_* tools ─────┼──write──┤ .build/llm_  │
  │ editor +   │   tested,    │ (main_dispatch.spl)    │  JSON/  │ dashboard/   │
  │ EditSession│   NOT yet    │                        │  JSONL  │ assistant/   │
  │            │   registered │ assistant store        │         │   (store)    │
  └─────┬──────┘   in server) └───────────────────────┘         └──────┬───────┘
        │ editor_mcp_dispatch(session, "editor.…", args)                │ read
        ▼                                                               ▼
   55 editor.* tools (open_file, read_buffer, edit, search,      assistant_bridge.spl
   diagnostics, goto_definition, lsp_*, wiki_*)                  + dashboard.views/assistant_*
```

- **Assistant core owns truth** (the store), **dashboard observes**, **bridge
  syncs** — never the source of truth. This is the KAIROS contract.
- The editor exposes a **55-tool `editor.*` MCP surface** via
  `editor_mcp_dispatch(session, tool_name, args)` (`src/app/editor/mcp_tools.spl`,
  registry `editor_mcp_tools()`), so an agent can drive the editor (open files,
  read buffers, edit, run LSP, navigate a wiki vault).

## Wired vs. contract-only — read this before relying on anything

**Verified / working**
- The 11 `assistant_*` tools are routed in `main_dispatch.spl` (`_is_in_process_tool` → `_dispatch_in_process`) and persist to the store.
- Dashboard views (`dashboard.views/assistant_*.spl`) + `assistant_bridge.spl` read the store and render session state (LIVE/ACTIVE/COMPLETED/FAILED/STALE/DEGRADED).
- The editor's 55 `editor.*` tools work in-process: exercised directly over an `EditSession` in `test/system/editor_controller_spec.spl`, `editor_md_wiki_index_spec.spl`, `editor_gui_spec.spl`.

**Contract-only / NOT wired (do not assume these run)**
- **`editor.*` is not registered in the MCP server.** `editor_mcp_tools()` /
  `editor_mcp_dispatch()` have **no caller** in `src/app/mcp/`; `main_dispatch.spl`
  contains no `editor.*` routing. The surface is a tested library API, not a
  live `simple mcp` endpoint. To make an agent drive the editor over MCP, this
  registration is the missing wire.
- **No editor→dashboard reverse channel.** No `editor_watcher`, no
  `.build/llm_dashboard/editor_events/` stream; the dashboard does not reflect
  live editor activity.
- **No "open in editor" dashboard action** and **no assistant/agent panel inside
  the editor** (`tui_shell_panels.spl` has diagnostics/LSP/wiki panels only).

## Common flows

- **Inspect agent sessions:** run `simple dashboard agents` (TUI) or its web mode;
  it reads `.build/llm_dashboard/assistant/`.
- **Control a session programmatically:** call the `assistant_*` MCP tools via the
  `simple mcp` server.
- **Drive the editor from code/tests today:** call
  `editor_mcp_dispatch(session, "editor.open_file", [path])` etc. directly (in-process).

## To finish the integration (roadmap)

1. Register `editor_mcp_tools()` in the MCP server dispatch so `editor.*` is a
   live endpoint (mirror the `assistant_*` wiring in `main_dispatch.spl`).
2. Add an editor→dashboard event stream + watcher for live activity.
3. Add a dashboard "open in editor" action and an assistant/agent panel in the
   editor shell (`src/lib/editor/view/`).

## See also
- `doc/07_guide/editor_tui.md` — editor components, rendering, status/blockers
- `doc/04_architecture/kairos_like_simple_mcp_llm_dashboard.md` — three-plane architecture
- `doc/04_architecture/mcp_lsp_dap_index.md` — MCP/LSP/DAP status index
