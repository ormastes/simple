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

Not yet started: K2-K6, P1-P3, X2-X4, L3-L4, H1-H3, E2.

## Feature Links

- Research: `doc/01_research/app/tools/notebook_lanes_research.md`
- Design/Architecture: `doc/05_design/app/tools/notebook_lanes_architecture.md`
- Plan: `doc/03_plan/agent_tasks/notebook_lanes_parallel_plan_2026-08-07.md`
- Guide (needs update as tasks land): `doc/07_guide/app/tools/jupyter.md`
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
  snb_sdn}.spl` (K1/L1); `src/app/simple_lab/{export_sdoctest,main,lab_executor}.spl`
  (L1/L2); `tools/jupyter/kernel_wrapper.py` (Python ZMQ transport, P0);
  `tools/jupyter/labextension/` (CM6 grammar, X1) with generator
  `scripts/gen_cm6_grammar.mjs`. Still to add: `magics.spl`, `remote_exec.spl`,
  `lane_locks.spl` (K3/K4/H2), the shared `local_exec.spl` (K2, will retire
  `lab_executor.spl`).

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
