---
name: verify
description: "Codex verification skill (primary verifier in cooperative mode). 6-phase production readiness verification: scope, SPipe quality, implementation stubs, requirements tracing, NFR, docs. STATUS: PASS/FAIL/WARN output. Must PASS before release."
---

# Verify — Codex (Primary Verifier)

**Cooperative Phase:** Verification (final gate before release)
**Self-sufficient.** Any LLM can run verify independently. Codex is the primary verifier in cooperative mode.

## Tools

- **Simple MCP** — query codebase structure, find stubs
- **Simple LSP MCP** — symbol lookup, dead code detection

## Usage

- No args: verify current changes
- File path: verify specific feature
- `--all`: full project verification

## 6-Phase Verification

### Phase 1: Scope Analysis

- Identify all files changed/added for the feature
- Map changes to requirements (REQ-NNN)
- Verify no unrelated changes sneaked in
- Run `sh scripts/audit/numbered-artifact-guard.shs --working` and
  `sh scripts/audit/numbered-artifact-guard.shs --staged`, then fail any
  newly added or renamed `*_1`, `*_2`, `part1`, `ver1`, `v1`, or equivalent
  numbered copy/version artifact. Existing files must be updated or split into
  meaningful domain/module names instead.

### Phase 2: SPipe Quality and Coverage

SPipe is owned by **design/implementation for creation** and by
**verify for acceptance**. Release must only consume a completed verify result;
release must not create, rewrite, or weaken SPipe evidence after verification.

- Every `it` block has real assertions (not `pass_todo`, not `expect(true).to_equal(true)`)
- Edge cases and error paths tested
- Every REQ-NNN has at least one test
- Every required SPipe generated/manual spec exists under `doc/06_spec/` at the
  path mirrored from the executable `test/...` spec
- Scenario-oriented generated docs read as manuals: primary scenario steps are
  visible first, `@inline`/`@prev` setup expands without redundant metadata,
  executable SPipe is folded by default, and advanced/edge/matrix/stress
  scenarios are folded or skipped according to policy.
- UI-facing specs include visible-state evidence when practical: TUI text/ANSI
  captures under `build/test-artifacts/<spec-relative-path>/`, GUI screenshots
  or goldens under `doc/06_spec/image/<spec-relative-path>/`, and embedded
  `**Screenshots:**` / `**TUI Captures:**` entries in generated docs
- Non-UI environmental specs include meaningful typed evidence when practical:
  `api`, `protocol`, `exec`, `binary`, `text`, `log`, or `artifact` captures
  attached to the relevant scenario step.
- Every BDD scenario has an executable or intentionally skipped SPipe `it` block with a concrete reason
- SPipe files are current with the final requirements/design; stale specs are a FAIL, not a release task
- Built-in matchers only: `to_equal`, `to_be`, `to_be_nil`, `to_contain`, `to_start_with`, `to_end_with`, `to_be_greater_than`, `to_be_less_than`
- Use `to_equal(true)` not `to_be_true()`
- For short grammar features, require runtime-specific evidence:
  - Interpreter specs for pipe-forward, composition, placeholder lambdas, method references, optional access, and compact DSL forms.
  - Native specs for only the compact forms intended to work in native mode.
  - Native evidence is invalid if the run reports codegen stub fallback; rerun with `SIMPLE_NO_STUB_FALLBACK=1`.
  - Specs that claim `:=` support must use the actual `:=` token, not equivalent `val` declarations.

### Phase 3: Implementation Stubs

Scan for stub patterns — any match is a **FAIL**:

- `pass_todo` — unimplemented placeholder
- `pass_do_nothing("why no-op is correct")` / `pass_dn("why no-op is correct")` with weak or missing rationale
- `todo("what remains", "hint or issue")` with weak or missing rationale
- Hardcoded returns without logic
- Empty function bodies
- Commented-out code blocks
- `# TODO` / `# FIXME` converted to `# NOTE` — hidden work
- Generated GPU backend source containing unsupported-operation placeholder
  comments or marker text instead of a diagnostic

**STUB001 = HARD FAIL.** No stubs in production code.

### Phase 4: Requirements Tracing

- Every REQ-NNN in `doc/02_requirements/feature/<feature>.md` traced to source code
- Every BDD scenario in `doc/06_spec/` has a matching `it` block in the mirrored
  executable `test/.../*_spec.spl` file
- `find doc/06_spec -name '*_spec.spl' | wc -l` returns `0`; executable specs
  under `doc/06_spec` are a hard layout failure
- Requirement, research, architecture/design, generated spec, plan,
  implementation, guide, and executable test links use the same feature slug or
  an explicit documented alias
- Any `doc/08_tracking/feature/feature_db.sdn` row with `status=done` fills
  `requirement`, `research`, `plan`, `architecture`, `design`, `system_spec`,
  `spec_doc`, `implementation`, `unit_tests`, `integration_tests`, and `guide`;
  confirm with `<runtime> lint doc/08_tracking/feature/feature_db.sdn`
- No orphan requirements (REQ without implementation)
- No orphan tests (tests without corresponding REQ)

### Phase 5: NFR Verification

- **Performance:** benchmarks exist for performance-critical paths
- **Security:** input validation present, no hardcoded secrets
- **Reliability:** error handling complete, `Result<T, E>` + `?` used consistently
- **Maintainability:** files under 800 lines, no duplication
- **Artifact naming:** no newly added/renamed numbered copy/version/part files
- **GUI/MDI evidence gates:** wrappers that claim live visual/event proof must
  fail when requested evidence is unavailable, times out, or only proves file
  existence. For Electron, Tauri mobile/iOS, hosted WM, QEMU/GTK WM, and pure WM
  evidence, require non-dummy event routing plus semantic screenshot/pixel
  checks for rendered windows and taskbar/dock icon or label regions. Explicit
  environment-based skips may pass only when the report says `skipped`, not when
  it claims live proof.
- **Core/MCP regression gate:** when compiler/core/lib or MCP/LSP files changed, require passing:
  - `<runtime> check src/compiler`
  - `<runtime> check src/lib`
  - `<runtime> check src/app/mcp`
  - `<runtime> check src/app/simple_lsp_mcp`
  - `SIMPLE_LIB=src <runtime> test test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter`
  - If npm packaging/release flow changed:
  - `<runtime> native-build --source src/compiler --source src/app --source src/lib --entry-closure --entry src/app/mcp/main.spl --strip --output build/bootstrap/mcp-package/simple_mcp_server`
  - `<runtime> native-build --source src/compiler --source src/app --source src/lib --entry-closure --entry src/app/simple_lsp_mcp/main.spl --strip --output build/bootstrap/mcp-package/simple_lsp_mcp_server`

### Phase 6: Documentation Freshness

- `doc/04_architecture/` updated for new modules
- `doc/05_design/` updated for new features
- `doc/06_spec/` generated/manual docs follow the mirrored `test/` layout
- Scenario manual guidance is followed for scenario-oriented specs; if not,
  return to design/implementation to improve the SPipe source and regenerate.
- Cross-references between docs intact
- CHANGELOG updated for user-facing changes

## Report Format

```
=== Verification Report: <feature> ===

[PASS] src/lib/feature.spl:42 — REQ-001 implemented with error handling
[PASS] test/lib/feature_spec.spl:15 — REQ-001 has 3 test cases
[FAIL] src/lib/feature.spl:87 — pass_todo found (STUB001)
[FAIL] test/lib/feature_spec.spl:30 — expect(true).to_equal(true) is not a real assertion
[WARN] doc/04_architecture/feature.md — not updated for new module

STATUS: FAIL (2 failures, 1 warning)
```

## Pass Criteria

- **Zero FAIL items** — any FAIL blocks release
- **WARN items reviewed** — warnings must be acknowledged
- **STATUS: PASS** required before release

## Artifacts Produced

| Artifact | Path |
|----------|------|
| Verification report | Printed to stdout / saved to `doc/09_report/verify_<feature>.md` |

## Rules

- NEVER downgrade a FAIL to WARN — fix the issue
- NEVER defer SPipe creation, cleanup, or requirement coverage updates to release
- NEVER skip stub detection — STUB001 is non-negotiable
- NEVER mark STATUS: PASS with outstanding FAILs
- If verification finds issues, report them — do not auto-fix without user approval
- Fail production wrapper verification if an MCP or LSP launcher executes a source entrypoint directly instead of a cached compiled artifact
- Audit hot request paths for repeated full scans, repeated file rereads, and per-request subprocesses; flag uncached patterns as FAIL or WARN based on impact
- Verify cache invalidation exists for write flows that affect cached or indexed data
- Require startup and representative request performance evidence for performance-sensitive tooling changes
- For `simple run` script-startup changes, require evidence from
  `test/02_integration/app/startup_argparse_mmap_perf_spec.spl` and confirm CLI
  argument scripts still avoid unnecessary compile/JIT startup unless
  `SIMPLE_EXECUTION_MODE` is explicitly set.
- Do not mark STATUS: PASS for compiler/core/lib or MCP/LSP work unless the matching runtime and MCP smoke checks passed
- Do not mark short grammar verification PASS when docs list a counterpart but executable tests only cover a longer equivalent form.
