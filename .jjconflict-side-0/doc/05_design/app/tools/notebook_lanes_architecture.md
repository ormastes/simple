# Notebook Execution Lanes — JupyterLab + Simple Lab: Architecture & Design

**Date:** 2026-08-07
**Status:** Design Proposal
**Research:** `doc/01_research/app/tools/notebook_lanes_research.md`
**Plan:** `doc/03_plan/agent_tasks/notebook_lanes_parallel_plan_2026-08-07.md`
**Linked design:** `doc/05_design/runtime/gpu_remote_interpreter_architecture.md` — this
document consumes its grammar (§2), `GpuLaneExecutor` (A3), GPU sessions (B3/B4, C3), and
the GMB-1 arena as the cross-cell state store. Its §8 lists the consumer contract.

---

## 1. Goals / Non-Goals

**Goals**
1. One **Kernel Session Manager** (Simple) serving three clients — Jupyter (ZMQ via the
   Python wrapper), `jupyter console`, and Simple Lab (in-process) — with per-session and
   per-cell execution modes selected by the existing composite spec strings.
2. Modes at parity with the test runner: `interpreter` (local),
   `interpreter(remote(baremetal(...)))` / `t32` / `openocd` / `ghdl`,
   `interpreter(remote(cuda(...)))` (incl. `resident`), `interpreter(remote(vulkan(...)))`,
   and the `jit(...)` variants where the lane supports them.
3. JupyterLab extension: highlighting, LSP, lane picker, math preview, SDoctest export.
4. Simple Lab notebook app on `app.ui.web` (S4), contract-tested via Protocol V1
   `UITestClient`, sharing 100% of the execution stack with the Jupyter kernel.
5. Hardening: extend the existing webserver hardening plan with notebook-specific auth,
   WebSocket, resource-limit, and lane-arbitration protections (§9).
6. Python remains a wrapper: every new wrapper feature is message plumbing; all decisions,
   parsing, session logic, and lane control are Simple code.

**Non-Goals (this phase)**
- ipywidgets/comm-based interactive widgets beyond the lane-picker comm.
- Multi-user collaborative editing (Simple Lab is single-user-per-token in v1).
- Debugger (DAP) integration into notebooks (tracked separately with the LSP/DAP guide).
- Replacing the local accumulation model (it stays for `interpreter`; see §5.2 upgrade
  note).

---

## 2. Architecture

```
┌────────────────┐   ┌──────────────────┐   ┌───────────────────────────────┐
│ JupyterLab /   │   │ jupyter console  │   │ Simple Lab (browser)          │
│ Notebook       │   │                  │   │ served by app.ui.web (S4)     │
└──────┬─────────┘   └──────┬───────────┘   └──────────────┬────────────────┘
       │ ZMQ wire proto      │ ZMQ                          │ HTTP + WebSocket
┌──────▼─────────────────────▼──────┐                       │ (Protocol V1 +
│ tools/jupyter/kernel_wrapper.py   │                       │  /api/lab/* NEW)
│ (transport ONLY: ZMQ↔JSON-lines)  │                       │
│ (recreated by Task P0 — the file  │                       │
│  is documented but not in-repo)   │                       │
└──────┬────────────────────────────┘                       │
       │ stdin/stdout JSON-lines            in-process call │
┌──────▼────────────────────────────────────────────────────▼────────────────┐
│ src/app/jupyter_kernel/main.spl  +  NEW src/lib/…/notebook/session_manager │
│  KernelSessionManager: sessions ▸ default mode ▸ per-cell overrides        │
│  magics: %mode %lanes %reset %budget …                                     │
└──────┬──────────────┬──────────────┬──────────────┬───────────────────────┘
       │              │              │              │   one NotebookExecutor per mode
┌──────▼─────┐ ┌──────▼─────┐ ┌──────▼─────┐ ┌──────▼─────┐
│ LocalExec  │ │ RemoteExec │ │ CudaExec   │ │ VulkanExec │
│ (existing  │ │ (JTAG/T32/ │ │ (SVM-G     │ │ (SVM-G     │
│ accumulate)│ │ OpenOCD/   │ │ resident / │ │ dispatch + │
│            │ │ GHDL sess.)│ │ per-launch)│ │ persistent │
│            │ │            │ │            │ │ arena)     │
└────────────┘ └────────────┘ └────────────┘ └────────────┘
```

Both front doors reach the **same** `KernelSessionManager`. The Jupyter path keeps the
existing process topology; Simple Lab links the manager in-process (no ZMQ, no Python).

## 3. Mode selection UX (reusing the composite grammar verbatim)

- **Session default:** kernelspec metadata key `simple_mode` (default `interpreter`);
  additional kernelspec variants can be installed (`Simple`, `Simple (CUDA)`,
  `Simple (RV32 QEMU)`) by `install.shs --mode='<spec>'` — each is just metadata, same
  kernel binary.
- **Magics (parsed in Simple, stripped before lowering):**
  - `%mode interpreter(remote(cuda(sm80(resident))))` — switch session default (tears down
    the old executor after confirmation output; state is lane-scoped, so this resets).
  - `%%mode interpreter(remote(vulkan(spv15)))` — first line of a cell: run this cell on
    that lane without changing the default (cross-lane state sharing is NOT provided; the
    cell sees only that lane's session state).
  - `%lanes` — print the lane availability table (reuses the host-aware probing from GPU
    plan A3/E2: `available` / `skip: <reason>` / `blocked: <reason>` per lane).
  - `%reset` — reset current lane session (local: clear accumulation; remote: reset target
    via the session's reset op; GPU: discard arena/VM state, keep device session).
  - `%budget 100000000` — set `SVMG_STEP_BUDGET` for subsequent GPU cells.
  - `%timeout 60000` — set `GPU_LANE_TIMEOUT_MS`-equivalent for subsequent cells.
  - `%onfault reset` — opt-in auto-reset after a remote target fault.
- Spec strings are validated by the **same extractor helpers** as the test runner
  (`src/lib/nogc_sync_mut/test_runner/test_executor_composite.spl`, extended by GPU plan
  A1). Invalid specs produce the runner's own diagnostic verbatim.

## 4. Execution semantics per lane

### 4.1 `NotebookExecutor` trait (NEW, `src/lib/nogc_sync_mut/notebook/executor.spl`)

```
trait NotebookExecutor:
    fn mode_spec() -> text
    fn probe() -> LaneStatus            # available | skip(reason) | blocked(reason)
    fn start(opts: SessionOpts) -> ()   # acquire device/board/process
    fn execute_cell(code: text, cell_id: text) -> CellResult
        # CellResult: stdout delta, display_data list, records, error?, duration
    fn interrupt() -> ()                # §5.3
    fn reset() -> ()
    fn shutdown() -> ()
```

`RemoteExec`/`CudaExec`/`VulkanExec` are thin adapters over the lane executors from the GPU
plan and the existing remote runner — the trait adds only session lifetime and cell
book-keeping. This is the single integration seam between the two plans.

### 4.2 Local (`interpreter`) — keep the existing model
Accumulation + subprocess re-execution + delta output + rollback stays as-is (it is tested
and fast to start; regression gate = `test/03_system/tools/jupyter/`). Upgrade note (out of
scope, tracked as a follow-up): a persistent interpreter process would make heavy cells
O(cell) instead of O(notebook); the trait above is written so `LocalExec` can swap
internals without touching clients.

### 4.3 JTAG / remote baremetal (`interpreter(remote(baremetal|t32|openocd|ghdl(...)))`)
- `start`: open the debug session once (QEMU spawn / OpenOCD+GDB / T32 / wlink per
  `doc/05_design/lib/runtime/remote_jit_combination_matrix.md`) and load the runtime
  scaffold; the connection lives for the whole notebook session.
- `execute_cell`: compile the **cell delta** against the session's known symbol state,
  upload to the target code region, run to completion (mailbox/semihost collection exactly
  as the lane already does), return output. Target memory persists ⇒ real incremental
  state.
- `reset`: target reset + scaffold reload. Board arbitration per §8.4.
- Error semantics: a target fault reports the fault record and leaves the session usable
  (auto-reset opt-in via `%onfault reset`).

### 4.4 CUDA (`interpreter(remote(cuda(smNN[(resident)])))`)
- **Resident (preferred for notebooks):** GPU plan B4's session — SVM-G VM stays loaded,
  arena persists, each cell is a program submitted through the command ring; VM globals in
  the DATA region carry state between cells. Live PUTC streams to the client as `stream`
  messages.
- **Per-launch (default when resident is refused/watchdog device):** the arena is retained
  across launches (allocated at `start`, freed at `shutdown`); each cell relaunches the VM
  with `entry_pc` for the new program; state persists via the arena, output is buffered
  and delivered at cell end.
- `jit(remote(cuda(...)))` cells: allowed; each cell body must be a complete kernel
  program; state sharing only through explicit arena reads/writes (documented limitation).

### 4.5 Vulkan (`interpreter(remote(vulkan(spvNN)))`)
- `start`: create instance/device/pipeline (cached), allocate arena — once.
- `execute_cell`: write SGP blob, one dispatch, fence, drain LOG/RECORD ⇒ outputs. Arena
  DATA persists across dispatches ⇒ incremental state, same model as CUDA per-launch.
- Interrupt = fence-timeout path; `VK_ERROR_DEVICE_LOST` ends the session with a clear
  message and marks the lane `blocked` until `%reset`.

## 5. Jupyter protocol completeness (wrapper grows plumbing only)

### 5.1 New message support (Simple side: `src/app/jupyter_kernel/`)
| Message | Backend |
|---|---|
| `complete_request` | forwarded to the Simple LSP (`textDocument/completion`) over a session-long LSP subprocess; positions mapped from cell text |
| `inspect_request` | LSP hover (`textDocument/hover`) |
| `interrupt_request` | `NotebookExecutor.interrupt()` — local: kill subprocess; JTAG: debugger halt; CUDA/Vulkan: force the watchdog/timeout path from the GPU design (§3.3 there) |
| `execute_request` extras | `display_data` for math blocks (`text/latex` from the m{} LaTeX backend, `text/plain` fallback from the Unicode backend) and for lane tables (`text/markdown`) |
| comm `simple_lane` | JSON: lane list + statuses + current mode; set-mode command — powers the JupyterLab lane picker (§6) |

### 5.2 Wrapper (`tools/jupyter/kernel_wrapper.py` — transport only; recreated by Task P0)
The wrapper does: connection-file parsing, the 5 ZMQ sockets, HMAC-SHA256 signing,
heartbeat, ZMQ multipart ↔ stdin/stdout JSON-lines — plus pass-through for
`complete_request`, `inspect_request`, `comm_open/comm_msg`, control-channel
`interrupt_request` (and SIGINT translation), `display_data` relay. No parsing of Simple
content in Python — every payload is opaque JSON produced in Simple.

### 5.3 Interrupt contract
Interrupt must never wedge a lane: each executor's `interrupt` resolves within
2×`timeout` worst-case by escalating (cooperative cancel → force path → session teardown
with `blocked:` status), mirroring the GPU plan's first-error-retention rule.

## 6. JupyterLab extension (`tools/jupyter/labextension/` — TypeScript, UI only)

The extension contains **no execution logic**; everything it shows comes from the kernel
comm or the LSP.

| Feature | Implementation |
|---|---|
| Syntax highlighting | CodeMirror 6 language package generated from the existing Tree-sitter grammar (same queries as `src/app/vscode_extension/`; conversion script checked in, output committed) |
| LSP features | register `.spl`/Simple with `jupyterlab-lsp`, spawning `bin/simple run src/app/lsp/main.spl` (same binary path the editors use) |
| Lane picker | toolbar dropdown bound to the `simple_lane` comm: shows lanes with ✓/skip/blocked and the reason on hover; selecting sends set-mode (i.e. runs `%mode` server-side) |
| Math preview | render `text/latex` display_data via JupyterLab's MathJax; inline m{} hover preview reuses LSP hover |
| SDoctest export | command palette: "Export notebook as SDoctest" → calls a kernel comm that runs the Simple exporter (§7.3) and saves `<name>.sdoctest.md` |
| Status | kernel status bar item showing current mode spec + step budget |

Packaging: prebuilt lab extension (`pip install`-able wheel or `jupyter labextension`
develop install) built in CI; `install.shs --with-lab` installs kernel + extension.

## 7. Simple Lab (notebook surface on Simple's own web stack)

### 7.1 App shape
- New app `src/app/simple_lab/` on the **Web Backend surface** (`app.ui.web`, S4), served
  by `SimpleHttpServer` (`src/lib/nogc_sync_mut/http_server/server.spl:20`) with `Router`
  (`router.spl:25`).
- Widgets through the semantic UI contract (`src/lib/common/ui/semantic_contract.spl`):
  notebook = list of cell widgets (editor area, output area, lane badge) + toolbar (run,
  run-all, lane picker, reset, export). Stable element IDs per the contract so the
  Protocol V1 `UITestClient` suite can drive it.
- Execution: `KernelSessionManager` linked **in-process** — no ZMQ, no Python anywhere in
  Simple Lab.
- Live output: WebSocket channel (same transport class as the existing web surface) for
  `stream`/`display_data` events; buffered lanes flush at cell end.

### 7.2 Document model
- **Interop:** open/save `.ipynb` (nbformat v4 subset: code + markdown cells, outputs as
  `stream`/`display_data`/`error`) so notebooks round-trip with JupyterLab.
- **Native:** `.snb.sdn` — an SDN-notebook format (cells as an SDN named table; metadata
  includes per-cell mode spec) consistent with the repo's SDN-backed databases. Converter
  `simple lab convert a.ipynb b.snb.sdn` both directions; conversion is lossless for the
  supported subset and fail-fast otherwise.

### 7.3 SDoctest bridge (shared with §6)
`src/app/simple_lab/export_sdoctest.spl`: cells → sdoctest blocks (code + captured output
as expected output), markdown cells pass through; result runnable by
`simple test --sdoctest <file>`. This turns any notebook into a verified doc — and gives
CI a way to regression-test notebooks without a browser.

### 7.4 API surface (NEW endpoints, versioned like Protocol V1)
```
GET  /api/lab/status           # version, auth mode, session count
GET  /api/lab/lanes            # lane availability table (same data as %lanes)
POST /api/lab/sessions         # create session {default_mode}
POST /api/lab/sessions/{id}/cells/{cid}/execute
POST /api/lab/sessions/{id}/interrupt | /reset
GET/PUT /api/lab/notebooks/{path}      # load/save (.ipynb | .snb.sdn)
WS   /api/lab/sessions/{id}/events     # stream/display_data/status frames
```
All responses carry `X-Lab-Protocol-Version: 1`.

## 8. Hardening (extends `webserver_hardening_optimization_plan_2026-05-26.md`)

### 8.1 Transport/server (adopt + verify existing track items on the Lab routes)
Bounded request line/header/body sizes; read/keep-alive timeouts; panic-free bad-request
handling; path-traversal refusal for notebook file routes (canonicalize + jail to the
notebook root); header canonicalization/duplicate policy. Each item gets a Lab-route spec
even where the lib already has one (defense in depth at the route layer).

### 8.2 Notebook-specific security
- **Auth:** random token per server start (Jupyter-style), required as `Authorization:
  Bearer` on every `/api/lab/*` call and as a query param on the WS upgrade; constant-time
  compare; localhost bind by default, non-localhost bind requires explicit
  `--allow-remote` + token.
- **WebSocket:** Origin allow-list check on upgrade; per-connection outbound queue bound
  with drop-oldest + client resync frame (backpressure rule from the hardening plan).
- **CSRF:** state-changing routes require the token header (no cookie auth in v1 ⇒ CSRF
  surface minimized by construction; documented explicitly).
- **Message bounds:** max cell size, max cells/notebook, max output bytes per cell
  (truncate with marker), max WS frame size — all configurable, all spec-tested.

### 8.3 Execution safety
- Cell code executes only through `NotebookExecutor`s ⇒ inherits every limit from the GPU
  design (step budgets, watchdogs, guard regions) and the remote runner (host-aware
  skips).
- Local lane subprocess: wall-clock timeout + output cap; workdir jailed to the session
  scratch dir.
- Resource ceilings per session: max concurrent executing cells = 1 (queue), max sessions
  per server (default 8).

### 8.4 Lane arbitration (boards and GPUs are exclusive resources)
New `src/lib/nogc_sync_mut/notebook/lane_locks.spl`: file-lock per physical resource key
(board serial/probe id, CUDA device UUID, Vulkan device index). Second session requesting
a held lane gets `blocked: lane held by session <id>` — the same wording style the lane
status specs already use. Locks are also honored by the test runner GPU lanes (shared
module) so notebooks and `bin/simple test` never fight over a device.

### 8.5 Robustness evidence
- Contract: extend the Protocol V1 shared suite
  (`test/system/ui/shared_ui_contract_spec.spl`) with Simple Lab (state query, command
  dispatch, read-after-write) — Simple Lab must reach **S4** like Web Backend.
- Load: bounded `wrk`-based smoke on `/api/lab/status` + a 100-cell execute soak on the
  local lane, under the crash-safe execution rules from the hardening plan (no parallel
  QEMU/bootstrap, loopback only, recorded limits).
- Fuzz-lite: malformed JSON bodies, oversized headers, truncated WS frames — all must
  produce 4xx/close without panic (panic = FAIL).
