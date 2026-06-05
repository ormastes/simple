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
- For `simple run` script-startup changes, require evidence from
  `test/02_integration/app/startup_argparse_mmap_perf_spec.spl` and confirm CLI
  argument scripts still avoid unnecessary compile/JIT startup unless
  `SIMPLE_EXECUTION_MODE` is explicitly set.
- Security: input validation, no secrets
- Reliability: error handling paths
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
- `find doc/06_spec -name '*_spec.spl' | wc -l` returns `0`; executable specs
  under `doc/06_spec` are a hard layout failure
- Cross-references intact

## Report Format

```
[PASS] file:line — description
[FAIL] file:line — reason
[WARN] file:line — concern
```

## Pass Criteria

- Zero FAIL items
- WARN items reviewed
- STATUS: PASS before release
- Do not defer SPipe fixes or coverage updates to release
- Do not mark PASS for compiler/core/lib or MCP/LSP work unless the matching smoke checks passed
