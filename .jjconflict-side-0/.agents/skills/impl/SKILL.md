---
name: impl
description: Implement a feature end-to-end. Self-sufficient — if research, requirements, or design are missing, creates them first. Covers implementation, testing, duplication check, refactoring, and verification.
---

# Impl — Self-Sufficient 15-Phase Workflow

**Self-sufficient.** If research, requirements, or design missing, does them first (phases 1-5).

## Prerequisites Check

| Artifact | Path | If exists, skip to |
|----------|------|--------------------|
| Research | `doc/01_research/local/<feature>.md` | Phase 4 |
| Requirements | `doc/02_requirements/feature/<feature>.md` | Phase 4 |
| Architecture | `doc/04_architecture/<feature>.md` | Phase 6 |
| Design | `doc/05_design/<feature>.md` | Phase 6 |
| System tests | `test/03_system/app/<app_name>/feature/<feature>_spec.spl` | Phase 8 |
| Generated spec docs | `doc/06_spec/03_system/app/<app_name>/feature/<feature>_spec.md` | Phase 8 |

**If ALL exist**, skip to Phase 8 (Implementation).

## Phases

1-3: Research + Requirements (skip if exist, otherwise do inline)
4-5: Plan + Design + Architecture (skip if exist)
6-7: System Test + Doc Consistency
8: Implementation in `src/**/<feature>.spl`
9-10: Unit + IT Tests (80%+ coverage) + Doctest
11-13: Bug Reports + Duplication Check + Refactoring
14: Full Test Suite (`bin/simple test test --whole --mode=interpreter` + `bin/simple lint <changed .spl files>`)
15: Run $verify + final smoke checks + VCS Sync

For compiler backend changes, add focused lint/spec coverage for invalid target
text such as `call nil`, `phi nil`, `getelementptr nil`, and raw LLVM result
type metadata. `LLVM001` must stay clean in LLVM emitter files.

## Rules

- All code in `.spl` — no Python, no Bash
- Stub Prevention: no `pass_todo` in final code, STUB001 = hard fail
- Shared-font work follows `.codex/skills/sp_dev/SKILL.md` “Shared multilingual
  font work”: preserve `FontRenderer`, transient `FontRenderBatch`, `WebIR`,
  `DrawIrComposition`, and the plan-defined frozen SSpec vocabulary; keep
  secondary detail steps folded.
- 80%+ branch coverage target
- For scenario-oriented specs, run the generated-manual review loop before
  claiming completion:
  `bin/simple spipe-docgen <spec> --output doc/06_spec --no-index`, read the
  output like a manual, then revise steps/captures/visibility until primary
  flows are manual-quality, noisy details are folded or skipped, and the
  generator reports `0 stubs`.
- If design introduced shared interface or manual setup/checker helper
  placeholders, implement them or keep them failing explicitly with
  `assert(false)` or `fail(...)`. Silent no-op helpers are not valid coverage.
- For broad lanes, preserve the cooperative review plan from design: lower-model
  sidecars such as Codex Spark, Claude Haiku, or Claude Sonnet must be merged or
  explicitly `N/A`, then a normal/highest-capability reviewer must accept broad
  findings, generated-manual quality, coverage claims, exclusions, and done
  marks before implementation handoff.
- When implementation changes workflow/tooling, evidence wrappers, generated
  specs, or verification contracts, update the matching `doc/07_guide`,
  `doc/06_spec`, `.codex/skills/`, `.agents/skills/`, `.claude/skills/`,
  `.claude/agents/spipe/`, and `.gemini/commands/` instructions before `$verify`; stale process docs are
  implementation work, not release cleanup.
- Do not mark implementation complete when workflow/tooling tests pass but the
  matching guide, skill, SPipe-agent, command, or generated/manual spec docs are
  stale. Documentation freshness is part of completion.
- For `simple_context` or context-mode changes, keep the MCP/tooling guide and
  mirrored generated manuals current. SQL-backed context paths must document the
  `--sql`/`--db`/`--source-filter` CLI flags, MCP `source_filter`, the
  file-optional `sql=true` plus non-empty `query` contract, embedded SQLite
  facade boundary, explicit absence statuses, and public-absence guard.
- Executable specs must stay under `test/`; generated/manual docs mirror that
  path under `doc/06_spec` after stripping the leading `test/` segment and must
  be `.md` only. Require
  `find doc/06_spec -name '*_spec.spl' | wc -l` to print `0` before sync.
- For `simple run` script-startup work, preserve the driver fast path for `.shs`,
  `get_cli_args`, and `std.cli` scripts; verify
  `test/02_integration/app/startup_argparse_mmap_perf_spec.spl` before claiming
  completion.
- Files > 800 lines must be split
- Run $verify before VCS sync
- If `src/compiler/**`, `src/lib/**`, `src/app/mcp/**`, `src/app/simple_lsp_mcp/**`, or MCP packaging files changed, finish with:
  - `<runtime> check src/compiler`
  - `<runtime> check src/lib`
  - `<runtime> check src/app/mcp`
  - `<runtime> check src/app/simple_lsp_mcp`
  - `SIMPLE_LIB=src <runtime> test test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter`
  - If publish/package flow changed:
  - `<runtime> native-build --source src/compiler --source src/app --source src/lib --entry-closure --entry src/app/mcp/main.spl --strip --output build/bootstrap/mcp-package/simple_mcp_server`
  - `<runtime> native-build --source src/compiler --source src/app --source src/lib --entry-closure --entry src/app/simple_lsp_mcp/main.spl --strip --output build/bootstrap/mcp-package/simple_lsp_mcp_server`
