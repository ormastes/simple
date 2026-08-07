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
- **L1** — `ipynb.spl`/`snb_sdn.spl` doc model + `src/app/simple_lab/export_sdoctest.spl`
  exporter. `.snb.sdn` is a dict-shaped SDN doc, not `Table` (SDN tables can't nest).
  Verify: ipynb round-trip 9/9, snb_sdn round-trip (incl. required
  `.ipynb`→`.snb.sdn`→`.ipynb` byte-stable case) 4/4, exporter 8/9 — the one RED example
  hits a pre-existing, unrelated `--sdoctest` subcommand defect
  (`unknown extern function: rt_string_ends_with`), filed separately rather than
  weakened.

Not yet started: K2-K6, P1-P3, X2-X4, L2-L4, H1-H3, E2.

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
  snb_sdn}.spl` (K1/L1); `src/app/simple_lab/export_sdoctest.spl` (L1);
  `tools/jupyter/kernel_wrapper.py` (Python ZMQ transport, P0);
  `tools/jupyter/labextension/` (CM6 grammar, X1) with generator
  `scripts/gen_cm6_grammar.mjs`. Still to add: `magics.spl`, `remote_exec.spl`,
  `lane_locks.spl` (K3/K4/H2).

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
