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
- For changed specs, `bin/simple spipe-docgen <spec> --output doc/06_spec --no-index`
  reports complete documentation with `0 stubs`; a generated manual marked as a
  stub is a FAIL even when the `.md` file exists.
- Scenario-oriented generated docs read as manuals: primary scenario steps are
  visible first, `@inline`/`@prev` setup expands without redundant metadata,
  executable SPipe is folded by default, and advanced/edge/matrix/stress
  scenarios are folded or skipped according to policy.
- Shared interface names and manual-facing setup/checker helper names match the
  accepted architecture/design/spec/manual references.
- CUDA font production trust must satisfy the canonical artifact rule in
  `.codex/skills/system_test/SKILL.md` before PASS.
- Shared-font interpreter calibration must satisfy `$system_test`: fail and
  empty fixtures each exit 1 with their distinct canonical marker; reject
  2/124/139 and retain commands, binary SHA-256, and logs at its artifact path.
- Placeholder helpers for shared interfaces or manual setup/checker flow fail
  explicitly with `assert(false)` or `fail(...)` until implemented; silent
  placeholder passes are a FAIL.
- For broad SPipe lanes, the recorded cooperative review plan is complete or
  explicitly `N/A`: lower-model sidecars such as Codex Spark, Claude Haiku, or
  Claude Sonnet were merged/reviewed when used, and the best available
  normal/highest-capability model accepted broad findings,
  generated-manual quality, coverage claims, exclusions, and done marks before
  PASS.
- UI-facing specs include visible-state evidence when practical: TUI text/ANSI
  captures under `build/test-artifacts/<spec-relative-path>/`, GUI screenshots
  or goldens under `doc/06_spec/image/<spec-relative-path>/`, and embedded
  `**Screenshots:**` / `**TUI Captures:**` entries in generated docs
- Non-UI environmental specs include meaningful typed evidence when practical:
  `api`, `protocol`, `exec`, `binary`, `text`, `log`, or `artifact` captures
  attached to the relevant scenario step.
- Every BDD scenario has an executable or intentionally skipped SPipe `it` block with a concrete reason
- SPipe files are current with the final requirements/design; stale specs are a FAIL, not a release task
- Canonical matchers in new specs: `to_equal`, `to_be`, `to_be_nil`,
  `to_contain`, `to_start_with`, `to_end_with`, `to_be_greater_than`,
  `to_be_less_than`
- Do not replace compatibility helpers with boolean-wrapper assertions. Assert
  concrete values, or use `to_be(true/false)` only when the boolean itself is
  the behavior under test.
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
- **Runtime facade boundary:** new env reads or process calls in app leaf
  code or `src/lib/gc_async_mut` outside owner modules such as `app/io/*.spl`
  must use the stdlib/app/gc env/process facades, not local `rt_env_get`,
  `rt_process_run`, `rt_process_run_timeout`, `rt_process_spawn_async`,
  `rt_process_wait`, `rt_process_is_running`, `rt_process_is_alive`, or
  `rt_process_kill`
  declarations/calls.
  Check with `sh scripts/audit/direct-env-runtime-guard.shs --working` and
  `sh scripts/audit/direct-env-runtime-guard.shs --staged`.
- **Artifact naming:** no newly added/renamed numbered copy/version/part files
- **Runtime boundary:** new direct `rt_*` extern use in Simple code is a FAIL
  unless it is an infrastructure/provider boundary or has a linked
  compiler/runtime performance or baremetal/direct-hardware blocker explaining
  why generated/native Simple cannot handle the path yet. Prefer stdlib,
  generated Simple, capability records, traits, or direct hardware backends over
  runtime bypasses.
- **Formal verification boundary:** use the proof system that matches the layer,
  and use both when the lane spans layers. RTL/hardware claims require
  RVFI/riscv-formal/SymbiYosys evidence; generated RISC-V RTL must pass
  `scripts/rtl/check-rvfi-formal-readiness.shs` with the core VHDL and, when
  emitted, `FORMAL_HARNESS`, `FORMAL_SBY`, and `FORMAL_MANIFEST`. A missing
  `sby` is readiness-only evidence, not a proof pass. Lean claims require
  `simple gen-lean verify`, `simple verify check`, or a lane-specific Lean
  wrapper with zero `sorry`/`admit`/untrusted axioms before claiming the modeled
  property is proven. Starvation, fairness, race-condition, scheduler, channel,
  lock, or resource-lifecycle changes require a concurrency/resource model
  check or an explicit blocker; a single interleaving test is not enough for a
  formal verification PASS.
  Generated Lean/BYL artifacts are not sufficient by themselves when manual
  constraints or theorem files exist; verify the stable manual proof entry
  point after regeneration and cite that exact gate in SPipe/report evidence.
  SimpleOS mission-critical release verification must run
  `sh scripts/check/check-simpleos-mission-critical-release.shs`; the hardening
  matrix readiness pass is not release completion while that gate reports
  blocked or failed, and PASS requires `release_blockers=none`. If blocked, run
  `sh scripts/check/check-simpleos-mission-critical-prereqs.shs` for the host
  dependency list and
  `sh scripts/setup/setup-simpleos-formal-env.shs --print-install` for setup
  commands. Treat `sidecar-contract-failed`, `missing-artifact`, and
  `sby-run-failed` as release-failing RTL evidence problems, not missing-tool
  blockers.
- **SimpleOS compiler-in-filesystem gate:** require a target-native Simple
  payload embedded in the install image at `/usr/bin/simple(.smf)`,
  `/bin/simple(.smf)`, `/sys/apps/simple(.smf)`,
  `/sys/apps/simple_compiler(.smf)`, `/sys/apps/simple_interpreter(.smf)`,
  `/sys/apps/simple_loader(.smf)`, and `/SYS/SIMPLETOOL.SDN`. PASS also needs
  in-guest `/usr/bin/simple --version` and compile/run `hello world` evidence
  from the mounted SimpleOS filesystem. Host `bin/simple`, placeholder marker
  apps, host-side compile/run, and QEMU fixed-command SSH responses are FAIL.
  Physical-board claims additionally need board identity, boot/download path,
  and serial or SSH transcript.
- **GUI/MDI evidence gates:** wrappers that claim live visual/event proof must
  fail when requested evidence is unavailable, times out, or only proves file
  existence. For Electron, Tauri mobile/iOS, hosted WM, QEMU/GTK WM, and pure WM
  evidence, require non-dummy event routing plus semantic screenshot/pixel
  checks for rendered windows and taskbar/dock icon or label regions. Explicit
  environment-based skips may pass only when the report says `skipped`, not when
  it claims live proof.
- **HTML-backed GUI interaction gates:** a static preview can pass live-browser
  event delivery only when it opens in Chromium/Electron and records trusted
  focus, keyboard/input, pointer, and click events against visible controls.
  Do not treat DOM shape, generated HTML, or screenshot existence as event
  handling proof.
- **GUI/web queue proof:** runtime queue/drain receipts are necessary evidence,
  not sufficient production proof. A GUI/web production pass requires same-frame
  backend `device_readback`, a positive backend handle, and matching checksum;
  runtime-only, synthetic-handle, upload-only, or CPU-mirror evidence is a FAIL.
- **GUI/web/2D RenderDoc+Vulkan gates:** start from
  `scripts/setup/setup-gui-web-2d-vulkan-env.shs --check|--run|--renderdoc-simple|--renderdoc`
  on POSIX hosts or `scripts/setup/setup-gui-web-2d-vulkan-env.ps1 -Check` on
  Windows. Require host Vulkan readiness, Simple Vulkan/Engine2D readback or
  RenderDoc proof, original Chrome RenderDoc proof, Electron RenderDoc proof,
  and production GUI/web parity evidence. If Chrome or Electron logs show
  `angle=vulkan` unavailable, report
  `vulkan-angle-unavailable` and fail the Vulkan proof even when pixels render.
  For Simple RenderDoc capture, leave `RDOC_SIMPLE_BIN` unset unless testing an
  explicit override; the helper must build/use the Rust interpreter carrying
  current `rt_renderdoc_*` externs.
  Browser runs with `RDOC_RENDERDOC_HOOK_CHILDREN=0` are diagnostic unless they
  still produce a Chrome/Electron GPU-process `.rdc` with valid `RDOC` magic;
  no-child-hook `missing-rdc` evidence remains a FAIL.
  Chromium `--in-process-gpu` evidence is also a FAIL on this Linux host unless
  it separately proves Vulkan remains active and emits valid browser `.rdc`
  evidence; current diagnostics show Vulkan unsupported or GPU crashes there.
- **GUI/web/2D source-coupling gate:** for rendering-lane implementation,
  wrapper, benchmark, or platform-agent patches, run
  `sh scripts/check/check-rendering-source-coupling.shs` against the working
  diff, or set `RENDERING_SOURCE_COUPLING_REVISION=<rev>` for a specific jj
  change. New raw `rt_*` calls, direct backend proof/status pokes, or forced
  backend pass states in rendering-scoped files are FAIL unless routed through
  an owning facade or the documented RenderDoc helper exception.
- **Metal/Vulkan/8K claims:** native Metal proof is macOS-only and must include
  raw Metal readback; Linux Metal is only `metal-requires-macos`. Vulkan claims
  need the readback/RenderDoc gate above. Any 8K performance claim needs a
  retained 8K row or an explicit blocker in `doc/09_report` / `doc/10_metrics`.
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
- Every final verification audits whether the lane changed `doc/07_guide`,
  generated/manual SPipe docs, or process skills, and fails stale or missing
  updates instead of deferring them to release cleanup.
- Scenario manual guidance is followed for scenario-oriented specs; if not,
  return to design/implementation to improve the SPipe source and regenerate.
- Workflow, tool-contract, evidence-wrapper, or verification-contract changes
  updated the matching `doc/07_guide`, `doc/06_spec`, `.codex/skills/`,
  `.agents/skills/`, `.claude/skills/`, `.claude/agents/spipe/`, and `.gemini/commands/`
  process docs before final verification.
- Cooperative lower-model sidecar review, if required by the SPipe state or
  plan, is complete before final verification; otherwise the verifier records
  why the lane is narrow enough for `N/A`.
- Cross-references between docs intact
- CHANGELOG updated for user-facing changes

## Report Format

```
=== Verification Report: <feature> ===

[PASS] src/lib/feature.spl:42 — REQ-001 implemented with error handling
[PASS] test/lib/feature_spec.spl:15 — REQ-001 has 3 test cases
[FAIL] src/lib/feature.spl:87 — pass_todo found (STUB001)
[FAIL] test/lib/feature_spec.spl:30 — expect(true).to_equal(true) is not a real assertion
[FAIL] doc/06_spec/03_system/app/feature/feature_spec.md — generated manual lacks readable scenario steps
[WARN] doc/04_architecture/feature.md — not updated for new module

STATUS: FAIL (3 failures, 1 warning)
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
- NEVER mark final verification PASS when workflow/tooling changes left stale
  `doc/07_guide`, `doc/06_spec`, `.codex/skills/`, `.agents/skills/`,
  `.claude/skills/`, `.claude/agents/spipe/`, or `.gemini/commands/` instructions behind
- NEVER mark the agent goal complete before that workflow/tooling doc freshness
  gate is satisfied or explicitly recorded as `N/A`
- NEVER skip stub detection — STUB001 is non-negotiable
- NEVER mark STATUS: PASS with outstanding FAILs
- If verification finds issues, report them — do not auto-fix without user approval
- Fail production wrapper verification if an MCP or LSP launcher executes a source entrypoint directly instead of a cached compiled artifact
- Audit hot request paths for repeated full scans, repeated file rereads, and per-request subprocesses; flag uncached patterns as FAIL or WARN based on impact
- Audit new `rt_*` use and fail runtime bypasses outside infrastructure/provider
  code unless a concrete direct-hardware or Simple-codegen/performance blocker
  is recorded.
- For `simple_context` or context-mode changes, verify the MCP/tooling guide,
  `doc/06_spec` manuals, and relevant skill/command docs mention any new
  `--sql`/`--db`/`--source-filter` behavior, MCP `source_filter`, file-optional
  SQL query shape, embedded SQLite facade boundary, and explicit absence
  statuses. Run `scripts/check/check-llm-tooling-public-absence-rendering.shs`.
- Verify cache invalidation exists for write flows that affect cached or indexed data
- Require startup and representative request performance evidence for performance-sensitive tooling changes
- For `simple run` script-startup changes, require evidence from
  `test/02_integration/app/startup_argparse_mmap_perf_spec.spl` and confirm CLI
  argument scripts still avoid unnecessary compile/JIT startup unless
  `SIMPLE_EXECUTION_MODE` is explicitly set.
- Do not mark STATUS: PASS for compiler/core/lib or MCP/LSP work unless the matching runtime and MCP smoke checks passed
- Do not mark short grammar verification PASS when docs list a counterpart but executable tests only cover a longer equivalent form.
