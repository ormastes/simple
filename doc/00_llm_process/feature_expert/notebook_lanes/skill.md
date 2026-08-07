# Feature Expert: Notebook Execution Lanes (Jupyter + Simple Lab)

## Role

Own feature-specific process knowledge for lane-aware notebooks: the Simple Jupyter
kernel, the (to-be-recreated) Python ZMQ transport wrapper, the JupyterLab extension, and
the Simple Lab web notebook surface.

## Status (2026-08-07)

Implementation in progress, parallel-agent execution against
`doc/03_plan/agent_tasks/notebook_lanes_parallel_plan_2026-08-07.md`. Landed:

- **P0** — `tools/jupyter/` (Python ZMQ transport wrapper, kernelspec, installer)
  recreated and verified: live `jupyter_client` round trip + `bin/simple test
  test/03_system/tools/jupyter/jupyter_kernel_install_system_spec.spl` (7/7). Plan-path
  correction: `test/03_system/tools/jupyter/` already existed (not absent as the plan
  assumed) with sibling P1-P3 specs. Doc drift found: the Rust seed's bootstrap banner
  leaks into notebook cell stdout via `session_execute`'s `2>&1` capture — needs a
  pure-Simple `bin/simple` redeploy to clear, tracked as a follow-up.
- **X1** — `tools/jupyter/labextension/` CodeMirror 6 grammar, generated from the
  compiler's real Tree-sitter queries (`src/compiler/10.frontend/parser/treesitter/
  queries/*.scm`, not `src/app/vscode_extension/` as the plan assumed — that extension
  only ships a hand-written TextMate grammar). Generator `scripts/gen_cm6_grammar.mjs`
  is SHA-gated against the `.scm` sources; Jest suite 4/4 green.
- **X2** — extension core + LSP wiring: `kernel.ts` stamps `language_info` on the
  notebook model (the kernel_wrapper doesn't send it, so CM6 highlighting never
  resolved without this); `status.ts` real status-bar `ModeStatusWidget` (shows
  `"local"` placeholder until X3 feeds live lane data); `lsp_server_spec.json` +
  `install.shs` wire `jupyter-lsp` to `bin/simple run src/app/lsp/main.spl`, verified
  end to end against a real `jupyter lab` (4.5.5) instance. Jest 19/19, `tsc -b` clean.
  **Blocker filed:** the labextension has no `pyproject.toml`/`hatch-jupyter-builder`
  packaging, so `jupyter labextension develop` can't load it — galata/browser
  verification for X2/X3/X4 is blocked until that's added (see
  `doc/08_tracking/bug/jupyter_labextension_missing_federated_build_packaging_2026-08-07.md`).
- **X3** — `tools/jupyter/labextension/src/lane.ts`: toolbar `LanePickerWidget`
  (`<select>` wrapped in a Lumino `Widget`, same style as `status.ts`) driven by a
  `LanePickerController` bound to the `simple_lane` comm (P1's
  `handle_comm_open`/`handle_comm_msg`/`lane_status_content`); selecting a lane sends
  `{set_mode}` with no optimistic update — the picker only ever reflects a
  server-confirmed `comm_msg` reply. `index.ts` hoists a single `ModeStatusWidget`
  instance shared between `mode-status` and the new `lane-picker` plugin so the status
  bar shows whichever notebook is currently active (`isActive` guard), and it stays
  live per notebook thereafter via the comm's own pushes. Math outputs needed **no**
  extension code: `@jupyterlab/rendermime`'s `defaultRendererFactories` already
  includes a `text/latex` factory whose `RenderedLatex` widget calls MathJax through
  the app-wide `ILatexTypesetter` token — verified against the vendored package
  source (`node_modules/@jupyterlab/rendermime/lib/{factories,renderers}.js`), not
  assumed. Two real gaps, not implementable from this stream: (1) P1 doesn't emit
  `text/latex` `display_data` for `m{}` blocks yet (kernel-side, out of X3 scope by
  design); (2) `ILatexTypesetter`'s provider, `@jupyterlab/mathjax-extension`, ships
  with the `jupyterlab` Python distribution, not as a dependency of this package —
  absent it, `RenderedLatex` degrades to raw source silently (no error) rather than
  failing loud. Design §6's "shows lanes with ✓/skip/blocked and the reason on
  hover" is not implementable either: P1's comm payload is a flat `{mode, lanes:
  string[]}`, no per-lane status field yet. galata verification stays blocked on the
  same federated-build packaging gap X2 filed. Verify: Jest 17/17 new
  (`tests/lane.test.ts`) + 48/48 full suite green, `tsc -b` clean. Also fixed a
  pre-existing break in `tests/index.test.ts` (missing `@jupyterlab/apputils` jest
  mock, left broken since X4 landed) while updating its plugin-count assertion.

- **K1** — `KernelSessionManager` + `NotebookExecutor` trait
  (`src/lib/nogc_sync_mut/notebook/{session_manager,executor,types}.spl`). GPU-A1's
  composite-grammar extractors were already landed, so `validate_mode_spec` calls the
  real `test_executor_composite_parse.spl` helpers directly (no stub needed). Verify:
  `bin/simple test test/01_unit/lib/notebook/` — 18/18. Found and filed a real fixer
  bug: `bin/simple fix` on `spipe_missing_docstrings` corrupts a bare `describe "..."`
  string literal.
- **K2** — `src/lib/nogc_sync_mut/notebook/local_exec.spl` (`LocalExec`/
  `LocalExecFactory`): accumulation/rollback/delta-output logic ported verbatim from
  pre-K2 `jupyter_kernel/main.spl`, which is now a thin JSON-lines front-end over
  `KernelSessionManager`. Fixed two real bugs while porting: (1) K1's
  `session_manager.spl` mutated a value-copy of the cached `KernelSession` without
  writing it back to `self.sessions[idx]`, silently discarding executor state after
  every call (cross-cell state loss); (2) `CellResult.is_ok()` treated an empty
  `error` string as success, but subprocess stderr is redirected into stdout so a
  real failure with blank `err` read as success. Verify: `test/03_system/tools/
  jupyter/` 22/22 (bit-identical to pre-K2 baseline), `jupyter_kernel_log_modes_spec`
  5/5, `test/01_unit/lib/notebook/` 18/18 (K1 regression).
- **K3** — `src/lib/nogc_sync_mut/notebook/magics.spl`: parses/strips `%mode`, `%%mode`,
  `%lanes`, `%reset`, `%budget`, `%timeout`, `%onfault` from leading cell lines only
  (a `%` later in code, e.g. `10 % 3`, is untouched); unknown magics error with the
  full supported list. Does not duplicate `%mode`/`%%mode` resolution — that stays in
  `session_manager.spl`; `dispatch_magics()` is the integration seam that calls
  `KernelSessionManager.set_default_mode`/`reset_session`/`default_mode_of` and returns
  the stripped code + any per-cell mode override for the caller to pass to
  `execute_cell`. `%budget`/`%timeout`/`%onfault` land in a `MagicsState` that's
  currently inert until GPU lanes (K5/K6) consume it via `SessionOpts`. Verify:
  `magics_spec.spl` 23/23 (incl. `%%mode` cell isolation, unknown-magic text,
  malformed-argument cases), `kernel_session_manager_spec.spl` 18/18 regression.
- **L1** — `ipynb.spl`/`snb_sdn.spl` doc model + `src/app/simple_lab/export_sdoctest.spl`
  exporter. `.snb.sdn` is a dict-shaped SDN doc, not `Table` (SDN tables can't nest).
  Verify: ipynb round-trip 9/9, snb_sdn round-trip (incl. required
  `.ipynb`→`.snb.sdn`→`.ipynb` byte-stable case) 4/4, exporter 8/9 — the one RED example
  hits a pre-existing, unrelated `--sdoctest` subcommand defect
  (`unknown extern function: rt_string_ends_with`), filed separately rather than
  weakened.

- **L2** — Simple Lab UI widget layer (`src/app/simple_lab/main.spl`,
  `SimpleLabApp`): toolbar (add cell/run all/reset) + per-cell panel
  (textarea editor, run button, lane badge, output text), stable element IDs
  documented in the module's header comment. Driven by `KernelSessionManager`
  (K1) in-process — no HTTP/WS (that's L3). K2 ("Port existing local
  execution behind `LocalExec`") hasn't landed yet, and the repo's
  anti-dummy-body rule forbids a fabricated/stub executor, so L2 ships its
  own small real-execution stand-in, `src/app/simple_lab/lab_executor.spl`
  (`LabLocalExec`/`LabLocalExecFactory`): per-instance accumulated cell
  source run through a real `bin/simple run` subprocess (same mechanism
  `session.spl` uses, but instance-scoped instead of module-global so
  concurrent sessions can't corrupt each other). Meant to be deleted and
  replaced by K2's shared `LocalExec` once that lands.
  Verify: `bin/simple test test/01_unit/app/simple_lab/lab_ui_semantic_spec.spl`
  — 4/4, S1-level (`semantic_ui_snapshot_from_state_with_capabilities`),
  driven entirely through `SemanticUiCommand` + `semantic_ui_command_to_event`
  (never raw widget-tree poking), covering cell add / source edit / run /
  output read-after-write with a real subprocess execution in the "run" case.
  **Bug filed:** matching the `UIEvent?` result of `semantic_ui_command_to_event`
  directly against enum-variant patterns (`match ev: UIEvent.Action(name): ...`)
  silently falls to the wildcard arm on this binary — pre-existing, also
  breaks 3 examples in `test/01_unit/app/ui/semantic_contract_spec.spl`.
  Worked around with a `!= nil` check instead of `match`; see
  `doc/08_tracking/bug/match_on_optional_enum_variant_falls_to_wildcard_2026-08-07.md`.

- **P1** — `src/lib/nogc_sync_mut/notebook/lsp_bridge.spl`: session-long Simple LSP
  subprocess bridge (real `rt_process_spawn_piped`-backed `StdioProcessTransport`
  from `std.editor.services.lsp_transport`, not the still-stub `LspClient` in that
  module). Real discovery: this repo's LSP completion/hover handlers shell out to
  `simple query completions/hover <path-from-uri> <line> <col>` against a REAL FILE
  ON DISK — `didChange` is a no-op there, no in-memory buffer — so the bridge
  rewrites a real temp file per call. Found + fixed a second bug:
  `query_sanitize.spl` allowlists only two `/tmp` prefixes for that CLI path;
  any other path silently returns empty with no error. `main.spl` wires
  `complete_request`/`inspect_request` (via the bridge), `interrupt_request`
  (idle-kernel/no-active-executor is a no-op success, not an error), and comm
  `simple_lane` (`comm_open` replies with mode + lane list;
  `comm_msg`'s `set_mode` calls `set_default_mode`). `display_data` for math
  blocks is deferred. Verify: `jupyter_execution_system_spec.spl` 7/7 (extended
  with interrupt/comm scenarios), `jupyter_kernel_log_modes_spec.spl` 5/5 and
  `jupyter_kernel_install_system_spec.spl` 7/7 regression-checked. `lsp_bridge_spec.spl`
  2/2, both SKIP-clean on a pre-existing, already-filed gap
  (`rt_process_spawn_piped` unwired in the interpreter's dispatch table,
  `doc/08_tracking/bug/interpreter_sffi_missing_piped_process_externs_2026-07-29.md`).

- **H2** — `src/lib/nogc_sync_mut/notebook/lane_locks.spl`: `LaneLockRegistry`
  (acquire/release/release_all_for_session/holder/is_held), generic string key
  shared by K4's remote lanes and a future GPU-lane consumer (GPU plan A3
  follow-up). Contention returns `"blocked: lane held by session <id>"` (matches
  `LaneStatus`'s wording); stale-lock takeover checks pid liveness via
  `rt_process_exists`. Verify: `lane_locks_spec.spl` 10/10 (contention, idempotent
  re-acquire, cross-key independence, shutdown release incl. cross-session refusal,
  stale-takeover with a real dead pid). **Design lesson** (not a new bug — the
  documented run-vs-test engine divergence): a `struct`-based registry mutated via
  free `fn`s passed under `bin/simple run` (JIT) but silently failed to persist
  mutations under the interpreter (`bin/simple test`'s engine) because the
  interpreter copies struct arguments at the call boundary — rewritten as a
  `class` with `me` methods (same shape as `KernelSessionManager`), which mutates
  correctly under both engines.

- **L3** — Simple Lab HTTP/WS API (`src/app/simple_lab/lab_server.spl`,
  `LabServer`): wires L2's in-process `KernelSessionManager` behind real
  HTTP/WS routes (`/api/lab/status`, `/lanes`, `/sessions`,
  `/sessions/:id/cells/:cid/execute`, `/interrupt`, `/reset`,
  `/notebooks/:name` GET/PUT, `/sessions/:id/events` WS upgrade). Plan-path
  correction: `SimpleHttpServer.handle_connection` unconditionally closes the
  socket after one request/response, so a WebSocket upgrade can't go through
  it — this module runs its own accept loop, reusing `Router`/`parse_request`/
  `write_response` for ordinary routes and hand-rolling only the WS handshake
  and frame writer (same shape as `app.ui.web.server.WebServer`). Streaming is
  buffered-at-cell-end (design §7.1): `execute` runs synchronously and appends
  `stream`+`status` frames to an in-memory per-session buffer that a
  `.../events` WS connection drains at connect time — a client must connect
  the WS stream before issuing `execute` to see it. Auth/hardening (token,
  origin allow-list) is explicitly out of scope, deferred to H1; server binds
  localhost-only. Still uses L2's `LabLocalExecFactory`
  (`lab_executor.spl`), not K2's shared `local_exec.spl` — see the L2 entry
  above. Verify: `bin/simple test
  test/03_system/tools/simple_lab/lab_http_api_spec.spl` (real subprocess +
  real loopback socket, create session -> execute -> WS events -> save/load
  notebook).

Landed since the above was written: **X3** (lane picker + math outputs,
`tools/jupyter/labextension/src/lane.ts`), **X4** (SDoctest export command,
`tools/jupyter/labextension/src/export.ts` + `main.spl`'s `simple_export`
comm), **P2** (wrapper plumbing fix: `interrupt_request` was fabricating a
fake `{"status":"ok"}` reply instead of relaying the kernel's real one —
fixed in `tools/jupyter/kernel_wrapper.py`), **P3** (E2E matrix, in flight).
**L3** landed (`src/app/simple_lab/lab_server.spl`, real HTTP/WS API) but its
system spec (`test/03_system/tools/simple_lab/lab_http_api_spec.spl`) needed
a poll-budget fix — 15s was far too short for this environment's ~50s
`bin/simple run` cold-start compile time, so `server.started` read `false`
even though the server genuinely came up; bumped to 150s, re-verifying now.

Not yet started or still landing: K5-K6 (GPU-dependent), L4 (protocol
contract / "reach S4", deps: L3), H1 (deps: L3), H3, E2.

## Feature Links

- Research: `doc/01_research/app/tools/notebook_lanes_research.md`
- Design/Architecture: `doc/05_design/app/tools/notebook_lanes_architecture.md`
- Plan: `doc/03_plan/agent_tasks/notebook_lanes_parallel_plan_2026-08-07.md`
- Guides: `doc/07_guide/app/tools/jupyter.md` (kernel);
  `doc/07_guide/app/tools/simple_lab.md` (Lab UI + HTTP/WS API, E1, added
  once L2/L3 landed) — both linked from `doc/07_guide/README.md` § Tooling
- Linked GPU-lane plan: `doc/03_plan/agent_tasks/gpu_remote_interpreter_parallel_plan_2026-08-07.md`
- Web contract: `doc/04_architecture/ui/shared_ui_contract.md`;
  hardening track: `doc/03_plan/compiler/perf/webserver_hardening_optimization_plan_2026-05-26.md`

## Source Entry Points

- Kernel: `src/app/jupyter_kernel/{main,protocol,session,render_adapter}.spl`;
  REPL sibling `src/app/repl/main.spl`.
- Specs: `test/03_system/tools/jupyter/` (NOT `test/03_system/jupyter/`), plus
  `test/system/jupyter/` and `test/02_integration/app/jupyter_kernel_log_modes_spec.spl`.
- Web stack: `src/lib/nogc_sync_mut/http_server/` (`SimpleHttpServer` server.spl:20,
  `Router` router.spl:25); UI contract `src/lib/common/ui/semantic_contract.spl`;
  contract spec `test/system/ui/shared_ui_contract_spec.spl`.
- LSP backend: `src/app/lsp/main.spl`; editor grammar donor: `src/app/vscode_extension/`.
- Landed: `src/lib/nogc_sync_mut/notebook/{session_manager,executor,types,ipynb,
  snb_sdn,magics,lane_locks,remote_exec,local_exec,lsp_bridge}.spl` (K1-K4/L1/H2/P1/K2);
  `src/app/simple_lab/{export_sdoctest,main,lab_executor,lab_server}.spl`
  (L1/L2/L3); `tools/jupyter/kernel_wrapper.py` (Python ZMQ transport, P0);
  `tools/jupyter/labextension/` (CM6 grammar, X1) with generator
  `scripts/gen_cm6_grammar.mjs`. K2's shared `local_exec.spl` has landed but
  is NOT yet wired into Simple Lab — `main.spl` and `lab_server.spl` both
  still construct `lab_executor.spl`'s `LabLocalExecFactory`; retiring it is
  still open. Not yet landed: K5-K6 (GPU-dependent), L4 (protocol contract).

## Known Constraints

- Python is transport-only (the one sanctioned wrapper); all logic in Simple. CI grep
  guards against payload inspection in the wrapper.
- No cross-lane state for `%%mode` cells; lane state is lane-scoped.
- Boards/GPUs are exclusive: lane_locks shared with the test runner.
- Local lane keeps the accumulate-and-re-execute model; remote/GPU lanes are true
  incremental sessions.

## Affected Layers

- [[test_runner]] — `doc/00_llm_process/layer_expert/test_runner/skill.md`
- ui/web surface, LSP, GPU lanes ([[gpu_remote_lanes]] —
  `doc/00_llm_process/feature_expert/gpu_remote_lanes/skill.md`)

## Update Rule

When research, requirements, architecture, design, tests, implementation, verification,
or release artifacts change for this feature, update this skill with the new links and
current handoff notes (per `.spipe/spipe/doc/00_llm_process/template/feature_skill.md`).
