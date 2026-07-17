---
name: verify
description: Production readiness verification. Checks SPipe tests for stubs/dummies, implementation completeness, requirement coverage, NFR targets, and architecture/design doc freshness. Self-sufficient — any LLM can run independently.
---

# Verify — Production Readiness Codex

**Self-sufficient.** Any LLM can run verify independently.

## Usage

- No args: verify current changes
- File path: verify specific feature
- `--all`: full project verification

## Checks

### 1. SPipe Tests
SPipe is verified here, before release. Release consumes `STATUS: PASS`; it does
not create, rewrite, or weaken SPipe after verification.

- Every `it` block has real assertions (not `pass_todo`, not `expect(true).to_equal(true)`)
- Edge cases and error paths tested
- Every REQ-NNN has test coverage
- Required executable SPipe specs exist under `test/...`; generated/manual
  scenario docs exist under the mirrored `doc/06_spec/.../*_spec.md` path
- For changed specs, `bin/simple spipe-docgen <spec> --output doc/06_spec --no-index`
  reports complete documentation with `0 stubs`; a generated manual marked as a
  stub is a FAIL even when the `.md` file exists.
- Shared-font interpreter diagnostics must use
  `build_interpreter_result_wrapper`; both
  `scripts/check/fixtures/font_evidence_runner_fail_spec.spl` must exit 1 with
  `test-runner: spec failed`, and
  `scripts/check/fixtures/font_evidence_runner_empty_spec.spl` must exit 1 with
  `test-runner: no examples executed`; reject 2/124/139 and retain commands,
  binary SHA-256, and logs. Native evidence remains authoritative.
- Scenario-oriented generated docs read as manuals: primary steps visible,
  inline/previous setup expanded, executable SPipe folded by default, detailed
  edge/matrix/stress/helper cases folded or skipped by policy.
- UI-facing specs include visible-state evidence when practical: TUI captures
  under `build/test-artifacts/<spec-relative-path>/`, GUI screenshots/goldens
  under `doc/06_spec/image/<spec-relative-path>/`, and embedded generated-doc
  metadata via `**Screenshots:**` or `**TUI Captures:**`
- Non-UI environmental specs include meaningful typed evidence when practical:
  API/protocol frames, command execution output, binary decode, text/logs, or
  artifacts attached to the relevant scenario step.
- Every BDD scenario has an executable or intentionally skipped SPipe `it` block with a concrete reason
- Stale, missing, placeholder, or requirement-disconnected SPipe is a FAIL
- Shared interface/manual helper names match the design/spec/manual references
- CUDA font production trust must satisfy the canonical artifact rule in
  `.codex/skills/system_test/SKILL.md` before PASS.
- The checker requires extracted optimization/font source bytes to match their
  emitter-declared hashes. Vulkan rejects missing/malformed hashes before compilation;
  a well-formed stale source may retain compiled `.comp`/`.spv` candidates for
  review, but remains invalid until both source and artifact pins match.
- Placeholder helper definitions fail explicitly with `assert(false)` or
  `fail(...)`; silent no-op helpers are a FAIL
- For broad SPipe lanes, the recorded cooperative review plan is complete or
  explicitly `N/A`: lower-model sidecars such as Codex Spark, Claude Haiku, or
  Claude Sonnet were merged/reviewed when used, and the best available
  normal/highest-capability model accepted broad findings,
  generated-manual quality, coverage claims, exclusions, and done marks before
  PASS.

### 2. Implementation
- No stub functions (`pass_todo`, weak `pass_do_nothing(...)`, weak `pass_dn(...)`, weak `todo(...)`)
- No hardcoded returns without logic
- Error handling complete, no commented-out code

### 3. Feature Requirements
- Every REQ-NNN traced to source code
- Every BDD scenario has matching `it` block
- Any `doc/08_tracking/feature/feature_db.sdn` row with `status=done` fills
  `requirement`, `research`, `plan`, `architecture`, `design`, `system_spec`,
  `spec_doc`, `implementation`, `unit_tests`, `integration_tests`, and `guide`;
  confirm with `<runtime> lint doc/08_tracking/feature/feature_db.sdn`

### 4. NFR
- Performance benchmarks exist
- GUI/MDI live evidence wrappers must fail when requested visual/event proof is
  unavailable, times out, or only proves artifact existence. Electron, Tauri
  mobile/iOS, hosted WM, QEMU/GTK WM, and pure WM proof must include non-dummy
  event routing plus semantic screenshot/pixel checks for rendered windows and
  taskbar/dock icon or label regions. Explicit skips may pass only when reported
  as skipped, not as live proof.
- GUI/web queue proof requires same-frame backend `device_readback`, a positive
  backend handle, and matching checksum. Runtime queue/drain receipts are
  necessary but not sufficient; runtime-only, synthetic-handle, upload-only, or
  CPU-mirror evidence is a FAIL.
- GUI/web/2D RenderDoc+Vulkan evidence must start from
  `scripts/setup/setup-gui-web-2d-vulkan-env.shs --check|--run|--renderdoc-simple|--renderdoc`
  on POSIX hosts or `scripts/setup/setup-gui-web-2d-vulkan-env.ps1 -Check` on
  Windows. Require host Vulkan readiness, Simple Vulkan/Engine2D readback or
  RenderDoc proof, original Chrome RenderDoc proof, Electron RenderDoc proof,
  and production GUI/web parity evidence. If Chrome or Electron logs show
  `angle=vulkan` unavailable, report
  `vulkan-angle-unavailable` and fail the Vulkan proof even when pixels render.
  `RDOC_RENDERDOC_HOOK_CHILDREN=0` and Chromium `--in-process-gpu` runs are
  diagnostic only unless they still produce valid browser GPU-process `.rdc`
  evidence with `RDOC` magic and prove Vulkan remains active.
- GUI/web/2D source-coupling verification must run
  `sh scripts/check/check-rendering-source-coupling.shs` for rendering-lane
  implementation, wrapper, benchmark, or platform-agent diffs. Set
  `RENDERING_SOURCE_COUPLING_REVISION=<rev>` to check a specific jj change.
  New raw `rt_*`, direct backend proof/status pokes, or forced backend pass
  states in rendering-scoped files are FAIL unless routed through an owning
  facade or the documented RenderDoc helper exception.
- Metal/Vulkan/8K claims require matching evidence: native Metal raw readback
  on macOS, `metal-requires-macos` for Linux Metal, the Vulkan gate above for
  Vulkan, and a retained 8K row or explicit blocker in `doc/09_report` /
  `doc/10_metrics` for 8K performance.
- For `simple run` script-startup changes, require evidence from
  `test/02_integration/app/startup_argparse_mmap_perf_spec.spl` and confirm CLI
  argument scripts still avoid unnecessary compile/JIT startup unless
  `SIMPLE_EXECUTION_MODE` is explicitly set.
- Runtime facade boundary: new env reads or process calls in app leaf code
  or `src/lib/gc_async_mut` outside owner modules such as `app/io/*.spl` must
  use the stdlib/app/gc env/process facades, not local `rt_env_get`,
  `rt_process_run`, `rt_process_run_timeout`, `rt_process_spawn_async`,
  `rt_process_wait`, `rt_process_is_running`, `rt_process_is_alive`, or
  `rt_process_kill`
  declarations/calls.
  Check with `sh scripts/audit/direct-env-runtime-guard.shs --working` and
  `sh scripts/audit/direct-env-runtime-guard.shs --staged`.
- Security: input validation, no secrets
- Reliability: error handling paths
- Formal verification boundary:
  - RTL/hardware claims use RVFI/riscv-formal/SymbiYosys evidence. Generated
    RISC-V RTL must pass `scripts/rtl/check-rvfi-formal-readiness.shs` with the
    core VHDL and, when emitted, `FORMAL_HARNESS`, `FORMAL_SBY`, and
    `FORMAL_MANIFEST`. Missing `sby` means readiness only, not proof pass.
  - Lean claims use `simple gen-lean verify`, `simple verify check`, or the
    lane-specific Lean proof wrapper with zero `sorry`/`admit`/untrusted axioms.
    Generated Lean/BYL artifacts must stay separate from manual theorem or
    constraint files; when manual proof files exist, rerun and cite the
    post-regeneration gate that checked that stable entry point.
  - Use both when the lane spans RTL plus higher-level Simple/spec behavior.
    Starvation, fairness, race-condition, scheduler, channel, lock, or resource
    lifecycle changes require a concurrency/resource model check or an explicit
    blocker; one interleaving test is not enough for formal verification PASS.
  - SimpleOS mission-critical release verification must run
    `sh scripts/check/check-simpleos-mission-critical-release.shs`; matrix
    readiness is not release completion while that gate reports blocked or
    failed, and PASS requires `release_blockers=none`. If blocked, run
    `sh scripts/check/check-simpleos-mission-critical-prereqs.shs` for the host
    dependency list and
    `sh scripts/setup/setup-simpleos-formal-env.shs --print-install` for setup
    commands. Treat `sidecar-contract-failed`, `missing-artifact`, and
    `sby-run-failed` as release-failing RTL evidence problems, not missing-tool
    blockers.
- SimpleOS compiler-in-filesystem verification requires a target-native Simple
  payload embedded in the install image at `/usr/bin/simple(.smf)`,
  `/bin/simple(.smf)`, `/sys/apps/simple(.smf)`,
  `/sys/apps/simple_compiler(.smf)`, `/sys/apps/simple_interpreter(.smf)`,
  `/sys/apps/simple_loader(.smf)`, and `/SYS/SIMPLETOOL.SDN`, then in-guest
  `/usr/bin/simple --version` and compile/run `hello world` evidence from the
  mounted SimpleOS filesystem. Host `bin/simple`, placeholder marker apps,
  host-side compile/run, and QEMU fixed-command SSH responses are FAIL. Board
  claims additionally need board identity, boot/download path, and serial or
  SSH transcript.
- Core/MCP regression gate for compiler/core/lib or MCP/LSP changes:
  - `<runtime> check src/compiler`
  - `<runtime> check src/lib`
  - `<runtime> check src/app/mcp`
  - `<runtime> check src/app/simple_lsp_mcp`
  - `SIMPLE_LIB=src <runtime> test test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter`
  - If npm packaging/release flow changed:
  - `<runtime> native-build --source src/compiler --source src/app --source src/lib --entry-closure --entry src/app/mcp/main.spl --strip --output build/bootstrap/mcp-package/simple_mcp_server`
  - `<runtime> native-build --source src/compiler --source src/app --source src/lib --entry-closure --entry src/app/simple_lsp_mcp/main.spl --strip --output build/bootstrap/mcp-package/simple_lsp_mcp_server`

### 5. Architecture & Design Docs
- `doc/04_architecture/` updated for new modules
- `doc/05_design/` updated for new features
- `doc/06_spec/` manual output reviewed for scenario quality when applicable
- Every final verification audits whether the lane changed `doc/07_guide`,
  generated/manual SPipe docs, or process skills, and fails stale or missing
  updates instead of deferring them to release cleanup.
- `find doc/06_spec -name '*_spec.spl' | wc -l` returns `0`; executable specs
  under `doc/06_spec` are a hard layout failure
- Workflow, tool-contract, evidence-wrapper, or verification-contract changes
  updated the matching `doc/07_guide`, `doc/06_spec`, `.codex/skills/`,
  `.agents/skills/`, `.claude/skills/`, `.claude/agents/spipe/`, and `.gemini/commands/`
  process docs before final verification
- Cooperative lower-model sidecar review, if required by the SPipe state or
  plan, is complete before final verification; otherwise the verifier records
  why the lane is narrow enough for `N/A`.
- Cross-references intact

## Report Format

```
[PASS] file:line — description
[FAIL] file:line — reason
[FAIL] doc/06_spec/03_system/app/feature/feature_spec.md — generated manual lacks readable scenario steps
[WARN] file:line — concern
```

## Pass Criteria

- Zero FAIL items
- WARN items reviewed
- STATUS: PASS before release
- Do not defer SPipe fixes or coverage updates to release
- Do not mark PASS when workflow/tooling changes left stale `doc/07_guide`,
  `doc/06_spec`, `.codex/skills/`, `.agents/skills/`, `.claude/skills/`,
  `.claude/agents/spipe/`, or `.gemini/commands/` instructions behind
- Do not mark the agent goal complete before that workflow/tooling doc
  freshness gate is satisfied or explicitly recorded as `N/A`
- For `simple_context` or context-mode changes, verify the MCP/tooling guide,
  generated manuals, and skill/command docs mention any new `--sql`/`--db`
  behavior, `--source-filter`/MCP `source_filter`, file-optional SQL query
  shape, embedded SQLite facade boundary, and explicit absence statuses. Run
  `scripts/check/check-llm-tooling-public-absence-rendering.shs`.
- Do not mark PASS for compiler/core/lib or MCP/LSP work unless the matching smoke checks passed
