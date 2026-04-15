---
name: impl
description: "Codex implementation skill. 15-phase workflow from research through verification. Self-sufficient — if research, requirements, or design missing, creates them first. Code in .spl only, 80%+ branch coverage, stub prevention gate."
---

# Impl — Codex Self-Sufficient 15-Phase Workflow

**Cooperative Phase:** Implementation (any step — self-sufficient)
**Self-sufficient.** If research, requirements, or design missing, does them first (phases 1-5).

## Tools

- **Simple MCP** — query codebase structure, module graph
- **Simple LSP MCP** — symbol lookup, type checking, go-to-definition
- **Context7 MCP** — external library documentation

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

### Phases 1-3: Research + Requirements
Skip if exist, otherwise do inline. See `research` skill for details.

### Phases 4-5: Plan + Design + Architecture
Skip if exist. See `design` skill for details.

### Phases 6-7: System Test + Doc Consistency
- Write SSpec BDD tests from design
- Verify doc cross-references are intact
- Built-in matchers only (see `design` skill for list)

### Phase 8: Implementation
- Implement in `src/**/<feature>.spl`
- Follow `/coding` rules strictly
- Reference: `doc/07_guide/quick_reference/syntax_quick_reference.md`

### Phases 9-10: Unit + Integration Tests
- 80%+ branch coverage target
- Write unit tests alongside implementation
- Write integration tests for cross-module interactions
- Add doctests for public API functions

### Phases 11-13: Bug Reports + Duplication Check + Refactoring
- Run `bin/simple bug-add` for any discovered bugs
- Check for code duplication across `src/`
- Refactor: files > 800 lines must be split

### Phase 14: Full Test Suite
```bash
bin/simple test && bin/simple build lint
```

### Phase 15: Verify + VCS Sync
- Run `verify` skill — must show STATUS: PASS
- VCS sync: `jj commit -m "feat: <feature description>"`

## Stub Prevention Gate

**STUB001 = HARD FAIL.** No `pass_todo` in final code.

Before declaring implementation complete, verify:
- No `pass_todo` anywhere in new/modified files
- No `pass_do_nothing` / `pass_dn` unless intentional no-op (documented)
- No hardcoded returns without logic
- No commented-out code blocks
- No empty function bodies

## Artifacts Produced

| Artifact | Path |
|----------|------|
| Implementation | `src/**/<feature>.spl` |
| Unit tests | `test/**/<feature>_spec.spl` |
| Integration tests | `test/**/<feature>_it_spec.spl` |
| Bug reports (if any) | Via `bin/simple bug-add` |

## Multi-LLM Collaboration

- If other LLMs produced research/design/tests, build on them
- Never overwrite existing artifacts — extend or improve
- Tag Codex-produced code with `# codex-impl` comment on module header if needed

## Rules

- All code in `.spl` — no Python, no Bash
- Generics use `<>` not `[]` — `Option<T>`, `List<Int>`
- Pattern binding: `if val` not `if let`
- Constructors: `Point(x: 3, y: 4)` not `.new()`
- `?` is operator only — never in names; use `.?` over `is_*` predicates
- NO inheritance — use composition, alias forwarding, traits, or mixins
- Use `Result<T, E>` + `?` for error handling (no try/catch/throw)
- Reserved keywords: `gen`, `val`, `def`, `exists`, `actor`, `assert`, `join`, `pass_todo`, `pass_do_nothing`, `pass_dn`
- NEVER over-engineer — only make requested changes
- NEVER add unused code — delete completely
- NEVER convert TODO/FIXME to NOTE — implement or delete
- Production MCP or LSP wrappers must execute cached compiled artifacts, not raw source entrypoints
- Do not place full-tree scans or repeated file rereads in request handlers when a cache or index is viable
- When cached or indexed data depends on writable files, implement explicit invalidation on create, edit, move, delete, rename, template application, and bulk replace flows
- Add perf smoke coverage for startup and representative hot requests when changing performance-sensitive tooling
