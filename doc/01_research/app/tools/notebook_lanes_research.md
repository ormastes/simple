# Notebook Execution Lanes — JupyterLab + Simple Lab: Research

**Date:** 2026-08-07
**Status:** Research complete (paths verified against the repo 2026-08-07)
**Design:** `doc/05_design/app/tools/notebook_lanes_architecture.md`
**Plan:** `doc/03_plan/agent_tasks/notebook_lanes_parallel_plan_2026-08-07.md`
**Linked plan:** `doc/03_plan/agent_tasks/gpu_remote_interpreter_parallel_plan_2026-08-07.md`
**Scope:** (1) Make the existing Simple Jupyter kernel lane-aware: local interpreter,
JTAG/remote-baremetal, CUDA, and Vulkan interpreter execution from notebook cells.
(2) A JupyterLab extension for Simple. (3) "Simple Lab" — a notebook surface served by
Simple's own web server GUI framework (`app.ui.web`), sharing the same session manager.
(4) Hardening of the web-server GUI infra that Simple Lab rides on.
**Rule inherited from the user requirement:** any Python code is a thin transport wrapper;
all logic lives in Simple scripts.

---

## 1. Jupyter infra — what exists, and one repo-reality correction

Documented in `doc/07_guide/app/tools/jupyter.md` and
`doc/09_report/2026/03/repl_jupyter_implementation_2026-03-11.md` (41/41 tests passing at
the time). **Verified against the working tree 2026-08-07:**

| Component | File | Verdict |
|---|---|---|
| Kernel process (all logic) | `src/app/jupyter_kernel/main.spl` + siblings `protocol.spl`, `session.spl`, `render_adapter.spl` | **EXISTS.** JSON-lines over stdio; handles `kernel_info`, `execute`, `is_complete`, `shutdown`, `comm_info`; session = accumulated code re-executed via subprocess; output delta tracking; failed-cell rollback |
| Python ZMQ bridge (transport only) | `tools/jupyter/kernel_wrapper.py` | **MISSING from the repo.** The guide and 2026-03 report describe it (~331 lines: connection-file parsing, 5 ZMQ sockets, HMAC-SHA256 signing, heartbeat, ZMQ multipart ↔ stdin/stdout JSON-lines), but no `tools/jupyter/` directory exists today. Recreating it is plan Task P0 |
| Kernelspec + installer | `tools/jupyter/kernel.json`, `tools/jupyter/install.shs` | **MISSING** (same gap — Task P0) |
| E2E + specs | `test/03_system/tools/jupyter/{jupyter_error,execution,kernel_install,notebook_server,state}_system_spec.spl`; also `test/system/jupyter/` and `test/02_integration/app/jupyter_kernel_log_modes_spec.spl` | **EXISTS** (note the real path is `test/03_system/tools/jupyter/`, not `test/03_system/jupyter/`). No Docker E2E script exists (`scripts/test/jupyter-docker-test.shs` is MISSING — Task P3 creates it if wanted) |
| REPL (shares the accumulation model) | `src/app/repl/main.spl` | **EXISTS.** Temp-file accumulation + subprocess; no compiler imports (fast startup) |

**Conclusion:** the Simple-side kernel is real and tested; the Python transport wrapper is
*documented but not present*. The wrapper-kernel split remains the required architecture —
the wrapper must be (re)created as pure message plumbing, never logic.

## 2. Gaps this effort closes

1. **No execution modes.** The kernel only runs the local toolchain. No hook into the
   composite mode grammar (`interpreter(remote(...))`) that the test runner already parses
   (`src/lib/nogc_sync_mut/test_runner/test_executor_composite.spl`).
2. **Accumulate-and-re-execute is incompatible with remote lanes.** Re-running the whole
   accumulated program per cell is fine locally but wrong on a JTAG board (side effects,
   seconds per upload) and wasteful on GPU sessions. Remote lanes need true incremental
   sessions.
3. **Protocol gaps:** no `complete_request`, `inspect_request`, `interrupt_request`, no
   `display_data` (rich outputs), no comms (needed for the lane picker UI).
4. **No ZMQ transport in-repo** (see §1) — blocks all real Jupyter clients.
5. **No JupyterLab extension:** no syntax highlighting, no LSP wiring, no lane picker.
6. **No Simple-native notebook surface** (the "Simple Lab" ask).

## 3. Web server GUI framework ALREADY EXISTS — Simple Lab builds on it

- **Web Backend surface `app.ui.web` is S4 (protocol-stable)**: HTTP + WebSocket, full
  HTML rendering, browser client, stable `/api/test` endpoints with
  `X-UI-Protocol-Version: 1`; semantic UI contract owned by
  `src/lib/common/ui/semantic_contract.spl`
  (`doc/04_architecture/ui/shared_ui_contract.md`; contract spec at
  `test/system/ui/shared_ui_contract_spec.spl`).
- **HTTP server lib**: `src/lib/nogc_sync_mut/http_server/` — 14 files;
  `class SimpleHttpServer` (`server.spl:20`), `class Router` (`router.spl:25`), plus
  h2/h3/tls servers, proxy, middleware, mime, parser, response, handler, types. Worked
  example under `examples/06_io/simple_web_server/`
  (`doc/05_design/ui/web/simple_web_server_lib_api.md`).
- **A webserver hardening track already exists**:
  `doc/03_plan/compiler/perf/webserver_hardening_optimization_plan_2026-05-26.md` — bounded
  request/header/body sizes, timeouts/keep-alive limits, panic-free bad-request handling,
  path-traversal refusal, header canonicalization, async runtime modernization, benchmark
  discipline. Simple Lab's hardening stream (H) extends this track instead of forking it.

## 4. Assets reused from elsewhere in the repo

| Asset | Reused for |
|---|---|
| Composite mode grammar + extractors (GPU plan A1; `test_executor_composite.spl`) | Notebook mode selection uses the identical spec strings — no new grammar |
| Remote runner routing + `GpuLaneExecutor` (GPU plan A3/B/C) | Lane executors become notebook session executors behind one trait |
| CUDA resident SVM-G session (GPU plan B4) | The natural CUDA notebook backend: VM + arena state persists across cells |
| Vulkan per-dispatch VM + persistent arena (GPU plan C3) | Cell = one dispatch; state lives in the arena DATA region between cells |
| Remote baremetal sessions (GDB RSP / T32 / OpenOCD / wlink adapters, `doc/05_design/runtime/remote_jit_architecture.md`) | JTAG notebook sessions keep the debug connection and target state alive across cells |
| Simple LSP (`src/app/lsp/main.spl`) | `complete_request` / `inspect_request` backend; JupyterLab LSP wiring |
| Tree-sitter grammar + VSCode extension (`src/app/vscode_extension/`) | CodeMirror 6 highlighting for the Lab extension |
| Math blocks `m{}` with the LaTeX render backend | Rich `display_data` (`text/latex`) outputs in both Jupyter and Simple Lab |
| SDoctest (`simple test --sdoctest`) | Notebook → SDoctest export: cells become verified executable docs |
| SDN format | Native notebook file format alongside `.ipynb` interop |

## 5. References

- `doc/07_guide/app/tools/jupyter.md`; `doc/09_report/2026/03/repl_jupyter_implementation_2026-03-11.md`
- `src/app/jupyter_kernel/{main,protocol,session,render_adapter}.spl`; `src/app/repl/main.spl`
- `test/03_system/tools/jupyter/`; `test/system/jupyter/`; `test/02_integration/app/jupyter_kernel_log_modes_spec.spl`
- `doc/04_architecture/ui/shared_ui_contract.md`; `src/lib/common/ui/semantic_contract.spl`; `test/system/ui/shared_ui_contract_spec.spl`
- `doc/05_design/ui/web/simple_web_server_lib_api.md`; `src/lib/nogc_sync_mut/http_server/`
- `doc/03_plan/compiler/perf/webserver_hardening_optimization_plan_2026-05-26.md`
- `doc/05_design/runtime/remote_jit_architecture.md`
- Jupyter: kernel wire protocol 5.x (shell/iopub/control/stdin/heartbeat), kernelspec
  format, nbformat v4, wrapper-kernel pattern, jupyterlab-lsp, galata testing
