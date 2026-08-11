# Simple Lab Guide

An in-repo, browser-style notebook UI for running Simple code cell-by-cell,
built on `app.ui.web`'s widget layer and the shared `KernelSessionManager`
execution core (the same engine the Jupyter kernel uses).

**Status (2026-08-07):** UI widget layer (L2) and the HTTP/WS API (L3) are
both implemented. The protocol-contract verification pass (L4, "reach S4")
has not landed yet, so the HTTP/WS surface is unreviewed against the repo's
hardening bar — treat it as a local dev tool, not yet a hardened service (see
§ Current Status and Limitations). See
`doc/03_plan/agent_tasks/notebook_lanes_parallel_plan_2026-08-07.md` for the
full task breakdown.

---

## Quick Start

### Run the UI Widget Layer (in-process)

`SimpleLabApp` (`src/app/simple_lab/main.spl`) is a widget-tree app built on
`common.ui.builder` / `common.ui.widget` — the same shape as other
`app.ui.web` MDSOC+ "outer" apps in this repo. Drive it like any other
Simple UI app, or exercise it directly in a spec via
`SimpleLabApp.create()` -> `build_ui()` / `handle_event()`. There is no
dedicated `bin/simple` CLI subcommand for it yet.

### Run the HTTP/WS API Server

```bash
bin/simple run src/app/simple_lab/lab_server.spl
```

Useful env vars (all optional, see `lab_server_main()` in
`src/app/simple_lab/lab_server.spl`):

| Var | Default | Meaning |
|-----|---------|---------|
| `SIMPLE_LAB_HTTP_PORT` | `0` (OS-assigned ephemeral port) | Port to bind on `127.0.0.1` |
| `SIMPLE_LAB_HTTP_MAX` | `1` | Number of connections to serve before exiting |
| `SIMPLE_LAB_HTTP_PORTFILE` | (none) | If set, the bound `host:port` is written to this file |
| `SIMPLE_LAB_HTTP_ACCEPT_TIMEOUT_MS` | `20000` | Accept-loop timeout per connection |
| `SIMPLE_LAB_NOTEBOOK_ROOT` | `lab_notebooks` | Directory notebooks are saved/loaded from |

The server prints `SIMPLE_LAB_LISTENING <addr>` once bound and
`SIMPLE_LAB_DONE` on clean exit — the same convention the repo's other
loopback test servers (e.g. `test/fixture/net/simple_http_server.spl`) use.

---

## Prerequisites

```bash
# Simple runtime must be built or deployed
bin/simple build --release
```

No Python or external packages are required — unlike the Jupyter kernel,
Simple Lab's server and UI are pure Simple end to end.

---

## Usage

### The UI: toolbar + cells

`SimpleLabApp.build_ui()` renders:

- **`lab_toolbar`** — a row of global actions: `+ Cell` (`lab_add_cell`),
  `Run All` (`lab_run_all`), `Reset` (`lab_reset`).
- **`lab_cells`** — one panel per cell (`cell_<n>`, 0-based, stable across
  adds), each containing:
  - `cell_<n>_editor` — a textarea holding the cell's source
  - `cell_<n>_toolbar` with a `Run` button (`cell_run_<n>`)
  - `cell_<n>_lane_badge` — text showing lane status (`"not run"`,
    `"available"`, or `"blocked: <reason>"`)
  - `cell_<n>_output` — the cell's last stdout delta or error text

All element IDs are stable per the semantic UI contract
(`src/lib/common/ui/semantic_contract.spl`), so a `UITestClient`/S4-style
suite can address them directly without re-deriving from render order — see
the full ID table in `src/app/simple_lab/main.spl`'s header comment.

Cells share one session (`lab_session_1`) and accumulate code across runs,
the same execution model the Jupyter kernel uses: `Run All` re-executes every
cell in order, `Reset` clears the session's accumulated state and every
cell's output/lane badge.

### The HTTP/WS API

Once `lab_server.spl` is running, every response carries an
`X-Lab-Protocol-Version: 1` header. Routes (`src/app/simple_lab/lab_server.spl`,
`lab_build_router()`):

| Method | Path | Purpose |
|--------|------|---------|
| `GET` | `/api/lab/status` | Server + session-count status |
| `GET` | `/api/lab/lanes?session_id=<id>` | `%lanes` magic result for a session |
| `POST` | `/api/lab/sessions` | Create a session (`{"default_mode": "..."}`) |
| `POST` | `/api/lab/sessions/:id/cells/:cid/execute` | Run a cell (`{"source": "...", "mode": "..."}`) |
| `POST` | `/api/lab/sessions/:id/interrupt` | Interrupt a lane |
| `POST` | `/api/lab/sessions/:id/reset` | Reset a session |
| `GET` | `/api/lab/notebooks/:name` | Load a saved `.ipynb`/`.snb.sdn` notebook |
| `PUT` | `/api/lab/notebooks/:name` | Save a notebook (validated by L1's parsers before write) |
| `GET` | `/api/lab/sessions/:id/events` (WebSocket upgrade) | Drain buffered `stream`/`status` frames for a session |

Execution is synchronous per `POST .../execute`: the server runs the cell,
then appends `stream` and `status` frames to that session's small in-memory
event buffer. A client that wants "live" delivery connects the `/events`
WebSocket **before** issuing the execute `POST` — the buffer is drained (and
cleared) at WS-connect time, not pushed proactively.

Notebook save/load is jailed to a flat directory (`SIMPLE_LAB_NOTEBOOK_ROOT`,
default `lab_notebooks/`) — single path segment only, `..` and nested paths
are rejected.

---

## How It Works

### Architecture

```
Browser / UITestClient
    |
    v  (widget events: Action / InputChange)
SimpleLabApp (src/app/simple_lab/main.spl)   -- L2, in-process widget layer
    |
    v  execute_cell(...)
KernelSessionManager (std.notebook.session_manager)  -- K1, shared with Jupyter
    |
    v  NotebookExecutor trait
LocalExec (std.notebook.local_exec)   -- K2, shared with the Jupyter kernel
    |
    v  subprocess: bin/simple run <accumulated cell source>
Simple runtime
```

```
HTTP/WS client (curl, browser, driver spec)
    |
    v  real TCP socket
LabServer.handle_connection (src/app/simple_lab/lab_server.spl)  -- L3
    |
    v  Router.dispatch (std.nogc_sync_mut.http_server.router)
lab_route_* handlers -> LAB_STATE.session_mgr (KernelSessionManager, same K1 core)
```

The HTTP server runs its own accept loop rather than the shared
`SimpleHttpServer.start()` helper: that helper unconditionally closes the
socket after each response, which can't support a WebSocket upgrade. See the
"Plan-path correction" comment at the top of `lab_server.spl` for the full
rationale and the other in-repo servers that use the same pattern
(`app.ui.web.server.WebServer`, `web_dashboard.terminal_ws`).

### Execution: K2's shared `LocalExec`

Both `main.spl` and `lab_server.spl` construct K2's shared local-lane
executor directly — there is no Lab-specific executor file. `main.spl`
imports `LocalExecFactory` from `std.notebook.local_exec`; `lab_server.spl`
imports the same class from
`std.nogc_sync_mut.notebook.local_exec` (`src/lib/nogc_sync_mut/notebook/local_exec.spl`).
`LocalExec` accumulates cell source per session and replays it through a real
`bin/simple run` subprocess — the same executor the Jupyter kernel uses.

### SDoctest export

`src/app/simple_lab/export_sdoctest.spl` converts a parsed notebook
(`.ipynb` or `.snb.sdn`, via L1's `ipynb.spl`/`snb_sdn.spl`) into a markdown
file of ` ```sdoctest ` fences, runnable with `simple test --sdoctest
<file>.md`. This turns a notebook into a regression-testable doc — see the
module's header comment for the exact prompt-prefix convention
(`>>> `/`... `) and how a cell with error output is exported as
` ```sdoctest:should_fail `.

---

## Testing

```bash
# UI widget layer (semantic UI commands, incl. real subprocess execution)
bin/simple test test/01_unit/app/simple_lab/lab_ui_semantic_spec.spl

# SDoctest exporter
bin/simple test test/01_unit/app/simple_lab/export_sdoctest_spec.spl

# HTTP/WS API — spawns lab_server.spl as a real OS process on a loopback port
bin/simple test test/03_system/tools/simple_lab/lab_http_api_spec.spl
```

The HTTP/WS spec is tagged `slow, system`: it drives the server as a separate
process over a real TCP socket (create session -> execute cell -> WebSocket
events -> save/load notebook), the same real-subprocess-plus-real-socket
pattern `test/helpers/browser_h1_loopback_driver.spl` uses, and for the same
reason — an in-process call can't prove anything about the actual wire
protocol.

---

## Source Files

| File | Purpose |
|------|---------|
| `src/app/simple_lab/main.spl` | `SimpleLabApp` — widget-tree UI (toolbar + per-cell panels), L2 |
| `src/app/simple_lab/lab_server.spl` | `LabServer` — HTTP/WS API + accept loop, L3 |
| `src/app/simple_lab/export_sdoctest.spl` | Notebook -> sdoctest markdown exporter, L1 |
| `src/lib/nogc_sync_mut/notebook/session_manager.spl` | `KernelSessionManager` — shared execution core, K1 |
| `src/lib/nogc_sync_mut/notebook/local_exec.spl` | `LocalExec`/`LocalExecFactory` — shared local-lane executor, K2, directly constructed by both `main.spl` and `lab_server.spl` |
| `src/lib/nogc_sync_mut/notebook/{ipynb,snb_sdn}.spl` | Notebook document models, L1 |
| `test/01_unit/app/simple_lab/lab_ui_semantic_spec.spl` | UI widget layer spec, L2 |
| `test/01_unit/app/simple_lab/export_sdoctest_spec.spl` | Exporter spec, L1 |
| `test/03_system/tools/simple_lab/lab_http_api_spec.spl` | HTTP/WS API system spec, L3 |

---

## Current Status and Limitations

- **No CLI subcommand yet** — launch via `bin/simple run
  src/app/simple_lab/lab_server.spl` (server) or drive `SimpleLabApp`
  directly (UI widget layer); there is no `bin/simple lab` entry point.
- **No auth/hardening yet** — the server binds `127.0.0.1` only and does not
  gate routes behind a bearer token (explicitly scoped to task H1, not yet
  landed). Do not expose it beyond localhost.
- **Protocol contract (L4) not yet landed** — the HTTP/WS surface exists and
  has a passing system spec, but the "reach S4" contract-verification pass
  that the plan gates further work behind has not landed. Treat the wire
  format as pre-1.0.
- **Execution uses K2's shared `LocalExec`**, constructed directly by both
  `main.spl` and `lab_server.spl` — see § How It Works above.
- **No JupyterLab-style rich display / widgets** — output is plain
  stdout-delta or error text.

---

## Related

- [Jupyter Kernel Guide](jupyter.md) — the sibling notebook surface; shares
  `KernelSessionManager` and the notebook document models with Simple Lab
- `doc/05_design/app/tools/notebook_lanes_architecture.md` — architecture
  (§7.1 UI widget layer, §7.3 sdoctest export, §7.4 HTTP/WS API)
- `doc/03_plan/agent_tasks/notebook_lanes_parallel_plan_2026-08-07.md` — task
  breakdown (Stream L)
- `doc/00_llm_process/feature_expert/notebook_lanes/skill.md` — feature
  process knowledge
