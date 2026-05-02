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
| System tests | `doc/06_spec/.../<feature>_spec.spl` | Phase 8 |

**If ALL exist**, skip to Phase 8 (Implementation).

## Phases

1-3: Research + Requirements (skip if exist, otherwise do inline)
4-5: Plan + Design + Architecture (skip if exist)
6-7: System Test + Doc Consistency
8: Implementation in `src/**/<feature>.spl`
9-10: Unit + IT Tests (80%+ coverage) + Doctest
11-13: Bug Reports + Duplication Check + Refactoring
14: Full Test Suite (`bin/simple test && bin/simple build lint`)
15: Run $verify + final smoke checks + VCS Sync

## Rules

- All code in `.spl` — no Python, no Bash
- Stub Prevention: no `pass_todo` in final code, STUB001 = hard fail
- 80%+ branch coverage target
- Files > 800 lines must be split
- Run $verify before VCS sync
- If `src/compiler/**`, `src/lib/**`, `src/app/mcp/**`, `src/app/simple_lsp_mcp/**`, or MCP packaging files changed, finish with:
  - `sh scripts/check-core-runtime-smoke.shs <runtime>`
  - `SIMPLE_BINARY=<runtime> sh scripts/check-mcp-native-smoke.shs`
  - If publish/package flow changed: `sh scripts/check-mcp-package-smoke.shs`
