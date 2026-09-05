# SPipe Notebook Skill — Jupyter/Codex Session Testing

Interactive notebook session specs verify multi-cell workflows without requiring
QEMU, CUDA, or Vulkan hardware. After any notebook execution, magics, or
`NotebookExecutor` trait change, run specs at the appropriate tier and verify
the session lifecycle (probe, skip-clean, execute, interrupt, reset).

## Session Lifecycle Specs

Notebook session testing separates unit and system tiers:

| Tier | Path | What it tests |
|------|------|---------------|
| **Unit** | `test/01_unit/lib/notebook/` | Session state, mode selection, magics parsing, lane locks, cell-delta execution without live Jupyter |
| **System** | `test/03_system/tools/jupyter/` | Live Jupyter protocol, kernel startup, cell execution, interrupt/reset over the wire |

### Unit Tier — Session Seam

Unit tests verify the `NotebookExecutor` trait
(`src/lib/nogc_sync_mut/notebook/executor.spl`) and its modes/magics without
live kernel. Test:

1. **Mode selection** — `%mode` and `%%mode` magics parse and route correctly
   (reuse composite spec grammar from `test_executor_composite_parse.spl`)
2. **Cell-delta execution** — changed cells execute, unchanged cells skip, lane
   probing (available/skip:/blocked:) reports correctly
3. **Magics routing** — `%lanes`, `%reset`, `%budget`, `%timeout`, `%onfault`
   parse and dispatch
4. **Lane locks** — mode/lane selection is atomic; concurrent cell changes don't
   corrupt state

Use `step("...")` for manual-first scenarios and `@manual: skip` for internal
plumbing that readers never see. Fail fast on unimplemented helpers with
`fail("TODO: ...")`.

### System Tier — Live Jupyter

System specs exercise live Jupyter sessions. Test:

1. **Session startup** — probe kernel availability, skip if absent (SKIP-clean)
2. **Cell execution** — submit code, read outputs/errors, assert state changed
3. **Interrupt/reset** — send interrupt signal, verify execution stops; reset
   clears state
4. **Error handling** — kernel exceptions propagate correctly, session remains
   usable after errors

Mark unavailable lanes with `skip()` using the shared probing vocabulary:
- `available: kernel` (live Jupyter available)
- `skip: no_kernel` (Jupyter not installed or not running)
- `blocked: cuda_required` (lane needs GPU, none available)
- `blocked: qemu_only` (can't run on host hardware)

### Spec Metadata

Use the same manual metadata as other scenarios:
- `# @inline` for reusable setup (session init, kernel probe)
- `# @prev("setup name")` to expand setup into the current scenario
- `# @capture(protocol)` for Jupyter wire protocol evidence (JSON frames)
- `# @manual: folded` for edge cases (timeout, concurrent cells)
- `# @manual: skip` for internal state checks

### Magics Reference

Notebook lanes use the same magics as the Jupyter frontend. Reference:
`doc/00_llm_process/feature_expert/notebook_lanes/skill.md` for the full
design and magics list. User-facing documentation: `doc/07_guide/app/tools/jupyter.md`.

### Quick References

- **Probe pattern (planned, not yet implemented):** `if probe_notebook_available(): ... else: skip()` —
  no such symbol exists in source yet; use the lane's own availability check
  (skip:/blocked: wording) until this helper lands.
- **Lane-gated helpers:** `start_jupyter_session()`, `execute_cell(code)`,
  `interrupt_session()`, `reset_session()`, `shutdown_session()`
- **Forbidden assertions:** Do NOT assert cross-lane state in `%%mode` cells.
  Do NOT hard-fail when a lane is absent — use SKIP-clean instead.

Before handoff: run `bin/simple spipe-docgen <spec> --output doc/06_spec --no-index`
for each notebook spec and require `0 stubs`. Generated manual must read as a
user-facing Jupyter session guide, not test plumbing.
