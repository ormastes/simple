# Notebook Execution Lanes — Parallel Implementation Plan

**Date:** 2026-08-07
**Status:** Ready (research + design landed; paths verified 2026-08-07)
**Research:** `doc/01_research/app/tools/notebook_lanes_research.md`
**Design:** `doc/05_design/app/tools/notebook_lanes_architecture.md` (§ numbers below refer to it)
**Linked plan:** `doc/03_plan/agent_tasks/gpu_remote_interpreter_parallel_plan_2026-08-07.md`
— task IDs `GPU-A1`, `GPU-A3`, `GPU-B3/B4`, `GPU-C3` below refer to it.
**Audience:** Written so Sonnet- or Haiku-class agents can execute each task independently.

Conventions identical to the GPU plan §0 (verify command mandatory; `[haiku-ok]` vs
`[sonnet]`; anti-dummy gate; bugs filed not worked around; if a stated path drifted, grep
for the symbol, use the real path, record the correction in the task report).

**Repo-reality note (2026-08-07):** `tools/jupyter/` (Python ZMQ wrapper, kernelspec,
installer) is documented in `doc/07_guide/app/tools/jupyter.md` but does NOT exist in the
tree — Task P0 recreates it. The Jupyter spec suite lives at
`test/03_system/tools/jupyter/` (not `test/03_system/jupyter/`). No Docker E2E script
exists; P3 creates it.

## 1. Dependency graph

```
K1 (session mgr + trait) ──► K2 (local exec port) ──► K3 (magics) ──► P1 (protocol msgs)
K1 ──► K4 (remote exec)      K1+GPU:B3/B4 ──► K5 (cuda exec)   K1+GPU:C3 ──► K6 (vulkan exec)
P0 (ZMQ wrapper + kernelspec) ──► P2 (wrapper plumbing) ; P1 ──► P2 ──► P3 (E2E matrix)
X1 (CM6 grammar) ─► X2 (labextension core) ─► X3 (lane picker+math) ─► X4 (sdoctest export UI)
L1 (doc model) ─► L2 (lab app UI) ─► L3 (lab API+WS) ─► L4 (S4 contract)
H1 (auth+bounds) ─► H2 (lane locks) ─► H3 (robustness evidence)
E1 (docs) no deps; E2 (CI) after P3, L4, H3
External deps: GPU-A1/A3 for K1's spec validation; GPU-B3/B4 for K5; GPU-C3 for K6.
K4 needs only the EXISTING remote runner (no GPU-plan dependency).
```

## 2. Stream K — Kernel session manager + lane executors (Simple)

**K1. `KernelSessionManager` + `NotebookExecutor` trait** `[sonnet]` `deps: GPU-A1 (spec validation only; stub validation behind a flag if A1 unlanded)`
- Files: new `src/lib/nogc_sync_mut/notebook/{session_manager.spl,executor.spl,types.spl}`
  + unit specs under `test/01_unit/lib/notebook/`.
- Steps: implement design §4.1 trait, session registry (id → default mode → executor
  cache), per-cell override resolution, `CellResult` type, `LaneStatus` type reusing the
  runner's `skip:`/`blocked:` wording. Spec validation calls the extractor helpers in
  `src/lib/nogc_sync_mut/test_runner/test_executor_composite.spl`.
- Verify: `bin/simple test test/01_unit/lib/notebook/` — session lifecycle, override
  resolution, invalid-spec diagnostic passthrough.

**K2. Port existing local execution behind `LocalExec`** `[haiku-ok]` `deps: K1`
- Files: `src/app/jupyter_kernel/main.spl` (+ `session.spl`) refactor:
  accumulation/rollback/delta logic moves into
  `src/lib/nogc_sync_mut/notebook/local_exec.spl`; kernel main becomes a thin JSON-lines
  front-end over `KernelSessionManager`.
- Behavior must be bit-identical: the existing Jupyter spec suite is the regression gate.
- Verify: `bin/simple test test/03_system/tools/jupyter/` — all existing specs pass
  unchanged (also run `test/02_integration/app/jupyter_kernel_log_modes_spec.spl`).

**K3. Magics** `[haiku-ok]` `deps: K2`
- Files: `src/lib/nogc_sync_mut/notebook/magics.spl` + unit spec.
- Steps: parse/strip `%mode`, `%%mode`, `%lanes`, `%reset`, `%budget`, `%timeout`,
  `%onfault` per design §3; unknown magics error with the supported list; magics never
  reach the lowering path.
- Verify: unit spec covers every magic incl. `%%mode` cell isolation and unknown-magic
  error text.

**K4. `RemoteExec` (JTAG/T32/OpenOCD/GHDL sessions)** `[sonnet]` `deps: K1`
- Files: `src/lib/nogc_sync_mut/notebook/remote_exec.spl`.
- Steps: wrap the existing composite remote runner per design §4.3: session start
  (spawn/attach once), cell-delta compile+upload+run+collect, fault handling, reset.
  Reuse the runner's probing for `probe()` verbatim.
- Verify: integration spec on the QEMU RV32 lane (`interpreter(remote(baremetal(riscv32)))`,
  QEMU host-tool-gated like existing specs): 3 cells with cross-cell state (val → fn →
  call), then `%reset`, then state gone; SKIP-clean without QEMU.

**K5. `CudaExec`** `[sonnet]` `deps: K1, GPU-B3; resident path GPU-B4`
- Steps: design §4.4 both submodes; live PUTC → stream frames in resident mode; arena
  persistence proof in per-launch mode.
- Verify: integration spec (CUDA host): cell1 writes VM global, cell2 reads it; interrupt
  mid-cell resolves per design §5.3; SKIP-clean without CUDA.

**K6. `VulkanExec`** `[sonnet]` `deps: K1, GPU-C3`
- Steps: design §4.5; DEVICE_LOST ⇒ session `blocked` until `%reset`.
- Verify: integration spec (Vulkan host): cross-cell arena state; fence-timeout interrupt;
  SKIP-clean without Vulkan.

## 3. Stream P — Jupyter transport + protocol

**P0. Recreate `tools/jupyter/` transport package** `[sonnet]` `deps: none`
- Files: new `tools/jupyter/kernel_wrapper.py` (transport ONLY: connection-file parsing,
  5 ZMQ sockets, HMAC-SHA256 signing, heartbeat, ZMQ multipart ↔ stdin/stdout
  JSON-lines), `tools/jupyter/kernel.json`, `tools/jupyter/install.shs` — matching what
  `doc/07_guide/app/tools/jupyter.md` documents. Python is allowed here as the ONE
  sanctioned transport wrapper (the repo's no-Python rule exception is exactly this
  boundary); zero language logic in Python.
- Verify: with `jupyter_client` installed, a kernel-info round trip and one `execute`
  against the existing kernel passes; `test/03_system/tools/jupyter/kernel_install_system_spec.spl`
  passes.

**P1. New protocol messages (Simple side)** `[sonnet]` `deps: K2 (K3 for %lanes comm data)`
- Files: `src/app/jupyter_kernel/` handlers per design §5.1 (extend `protocol.spl`); LSP
  subprocess session module `src/lib/nogc_sync_mut/notebook/lsp_bridge.spl`.
- Verify: extend `test/03_system/tools/jupyter/execution_system_spec.spl` (or a sibling)
  with complete/inspect/interrupt/display_data/comm scenarios (LSP-gated host-aware).

**P2. Wrapper plumbing (Python, transport only)** `[haiku-ok]` `deps: P0, P1`
- Files: `tools/jupyter/kernel_wrapper.py`.
- Steps: design §5.2 pass-throughs; control-channel interrupt + SIGINT; comm relay. Diff
  review rule: the PR must show zero content inspection of Simple payloads (mechanically
  checkable: no key access beyond envelope fields).
- Verify: a helper script under `test/03_system/tools/jupyter/helpers/` exercises
  complete + interrupt + comm round-trip.

**P3. E2E matrix incl. lanes** `[haiku-ok]` `deps: P2, K4–K6 as available`
- Files: new nbconvert fixtures `mode_local.ipynb`, `mode_qemu_rv32.ipynb`,
  `mode_cuda.ipynb`, `mode_vulkan.ipynb`; NEW Docker E2E script
  `scripts/test/jupyter-docker-test.shs` (none exists today) — local + QEMU lanes run in
  container; GPU fixtures run on labeled runners only.
- Verify: `sh scripts/test/jupyter-docker-test.shs` green; GPU fixtures green on
  `cuda-live`/`vulkan-live` runners.

## 4. Stream X — JupyterLab extension (TypeScript, UI only)

**X1. CodeMirror 6 grammar from Tree-sitter** `[sonnet]` `deps: none`
- Files: `tools/jupyter/labextension/` scaffold + `scripts/gen_cm6_grammar.*` conversion
  from the VSCode extension's Tree-sitter queries (`src/app/vscode_extension/`);
  committed generated output + SHA gate.
- Verify: extension unit test highlights a fixture `.spl` cell with expected token classes.

**X2. Extension core + LSP wiring** `[sonnet]` `deps: X1`
- Steps: register language/kernel mapping; `jupyterlab-lsp` server spec pointing at
  `bin/simple run src/app/lsp/main.spl`; status-bar mode item.
- Verify: `jupyter lab` smoke script (headless galata test) — completion popup appears for
  a stdlib symbol.

**X3. Lane picker + math outputs** `[sonnet]` `deps: X2, P1`
- Verify: galata test — picker lists lanes from the comm; selecting a lane updates the
  status item; a `m{}` cell renders MathJax output.

**X4. SDoctest export command** `[haiku-ok]` `deps: X2, L1 (shared exporter)`
- Verify: galata test exports fixture notebook; `bin/simple test --sdoctest <out>` passes.

## 5. Stream L — Simple Lab

**L1. Document model + SDoctest exporter** `[sonnet]` `deps: none`
- Files: `src/lib/nogc_sync_mut/notebook/{ipynb.spl,snb_sdn.spl}`,
  `src/app/simple_lab/export_sdoctest.spl` + unit specs.
- Steps: design §7.2 nbformat-v4 subset reader/writer (fail-fast outside subset), SDN
  notebook format, lossless converters, design §7.3 exporter.
- Verify: round-trip specs (`.ipynb`→`.snb.sdn`→`.ipynb` byte-stable for the subset);
  exporter output passes `--sdoctest` on the hello fixture.

**L2. Lab app UI on `app.ui.web`** `[sonnet]` `deps: L1, K1`
- Files: `src/app/simple_lab/main.spl` + widgets via the semantic contract
  (`src/lib/common/ui/semantic_contract.spl`); stable element IDs documented in the
  design doc.
- Verify: headless semantic-state spec (S1/S2 level): cell add/edit/run/output
  read-after-write through shared helpers.

**L3. Lab HTTP/WS API** `[sonnet]` `deps: L2, K3`
- Steps: design §7.4 routes on `SimpleHttpServer` (`src/lib/nogc_sync_mut/http_server/`);
  WS event frames; version header.
- Verify: system spec drives create-session → execute → stream frames → save `.snb.sdn`
  over real HTTP/WS on loopback.

**L4. Protocol V1 contract (reach S4)** `[sonnet]` `deps: L3`
- Steps: implement `/api/test/...` per `doc/04_architecture/ui/shared_ui_contract.md` via
  the shared `handle_test_request` handler; add Simple Lab to the cross-surface contract
  suite.
- Verify: `bin/simple test test/system/ui/shared_ui_contract_spec.spl` (extended) passes
  with Simple Lab listed as an S4 surface.

## 6. Stream H — Hardening

**H1. Auth + bounds on Lab routes** `[sonnet]` `deps: L3`
- Steps: design §8.1–§8.2 complete; every limit configurable with safe defaults;
  localhost-bind default.
- Verify: hardening spec — no-token 401, bad-origin WS refused, oversized body 413,
  traversal path 403, malformed JSON 400 without panic, output-cap truncation marker.

**H2. Lane locks** `[sonnet]` `deps: K4 (keys), K5/K6 for GPU keys`
- Files: `src/lib/nogc_sync_mut/notebook/lane_locks.spl` shared with the test runner GPU
  lanes (GPU plan A3 consumes it in a follow-up patch noted in its report).
- Verify: unit spec — two sessions contend for one fake key: second gets `blocked: lane
  held by session <id>`; lock released on shutdown and on process death (stale-lock
  takeover with pid check).

**H3. Robustness evidence** `[haiku-ok]` `deps: H1, L4`
- Steps: design §8.5 load smoke + 100-cell soak + fuzz-lite corpus, under the existing
  crash-safe execution rules (no parallel QEMU/bootstrap; loopback; recorded limits).
- Verify: perf/robustness report checked into `doc/09_report/` with commands + numbers;
  zero panics.

## 7. Stream E — Docs + CI

**E1. Docs — landed with this plan** `[haiku-ok]` `deps: none`
- The research/design/plan split is DONE (this document set). Remaining: update
  `doc/07_guide/app/tools/jupyter.md` (modes, magics, labextension install, and the
  P0 wrapper-recreation status) and add `doc/07_guide/app/tools/simple_lab.md` when L2
  lands; link both from the docs hub and the webserver hardening plan's source list;
  refresh `doc/00_llm_process/feature_expert/notebook_lanes/skill.md` as tasks land.
- Verify: doc link check; `%lanes` output sample in the guide matches the implementation.

**E2. CI wiring** `[haiku-ok]` `deps: P3, L4, H3`
- Jobs: kernel+Lab spec suites on all runners; Docker Jupyter E2E; galata extension tests;
  GPU notebook fixtures on `cuda-live`/`vulkan-live`; board fixtures stay
  manual/host-aware.
- Verify: green pipeline run linked in the report.

## 8. Suggested schedule (3 agents)

| Slot | Agent 1 | Agent 2 | Agent 3 |
|---|---|---|---|
| 1 | K1 → K2 | L1 | P0 → X1 |
| 2 | K3 → K4 | L2 | X2 |
| 3 | P1 → P2 | L3 → L4 | K5/K6 (as GPU plan lands) |
| 4 | P3 | H1 → H2 → H3 | X3 → X4, E1/E2 |

Critical path: K1→K2→K3→P1→P2→P3 and L1→L2→L3→L4→H1. K5/K6 track the GPU plan's B3/B4/C3
and can land last without blocking anything else.

## 9. Risks

| Risk | Mitigation |
|---|---|
| Accumulation refactor (K2) regresses the working kernel | Existing `test/03_system/tools/jupyter/` suite is the hard gate; behavior must be bit-identical before any new feature lands |
| The wrapper never existed in-tree, so "recreate per the guide" may drift from what the 41/41 report tested | P0's verify is a live `jupyter_client` round trip, not a doc citation; the kernel_install system spec is the gate |
| Cross-lane state confusion (`%%mode` cells) | Explicitly no cross-lane state (design §3); the magic's confirmation output names the lane whose state the cell saw |
| Wrapper scope creep into Python logic | P2's mechanical review rule (no payload key access beyond envelope) + repo grep in CI for `json.loads(...)['content']['code']`-style access |
| Board/GPU contention between notebooks and `bin/simple test` | H2 lane locks shared by both consumers |
| Web surface security regressions | H1 specs are FAIL-on-panic; Lab reaches S4 only after the contract suite passes (L4 gate) |
| GPU plan slippage blocks this plan | Only K5/K6 depend on it; everything else ships against local + JTAG lanes |
