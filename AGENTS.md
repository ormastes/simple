# Codex Agent — Self-Sufficient Feature Pipeline

**Full pipeline (ideal):** `$research` -> `$design` -> `$impl` -> `$verify` -> `$release`

Each step is **self-sufficient** — if prior steps were not done (by Claude, Gemini, or anyone), do them yourself before proceeding.

## Cooperative Phase Dev

In multi-LLM cooperative mode, Codex owns **Step 2 (research)** and **Step 4 (architecture+design)**:
```
Step 1: Claude /research  →  Step 2: Codex $research  →  Step 3: Gemini /design (UI)
→  Step 4: Codex $design (arch)  →  Step 5: Claude /design (quality)
```
See: `doc/guide/llm_cooperative_dev_phase.md`

## Skills Reference

| Skill | File | Purpose |
|-------|------|---------|
| `$research` | `.codex/skills/research/SKILL.md` | Research + requirement options |
| `$design` | `.codex/skills/design/SKILL.md` | Architecture + system tests |
| `$impl` | `.codex/skills/impl/SKILL.md` | 15-phase implementation |
| `$verify` | `.codex/skills/verify/SKILL.md` | Production readiness check |
| `$release` | `.codex/skills/release/SKILL.md` | Version bump + tag |
| `$architecture` | `.codex/skills/architecture/SKILL.md` | MDSOC, ADR writing |
| `$mdsoc` | `.codex/skills/mdsoc-architecture-writing/SKILL.md` | MDSOC architecture docs |
| `$system_test` | `.codex/skills/system_test/SKILL.md` | SSpec test design |
| `$coding` | `.codex/skills/coding/SKILL.md` | Simple language rules |

---

## Self-Sufficiency Rule

Before starting any step, **check if prerequisite artifacts exist**:

| If you need... | Check for... | If missing... |
|----------------|-------------|---------------|
| Research | `doc/01_research/local/<feature>.md` | Do local + domain research yourself |
| Requirements | `doc/02_requirements/feature/<feature>.md` | Research first, then generate + ask user to select |
| UI design | `doc/05_design/<feature>_tui.md` | Create TUI/GUI mockups yourself |
| Architecture | `doc/04_architecture/<feature>.md` | Design architecture yourself |
| System tests | `doc/06_spec/app/<app_name>/feature/<feature>_spec.spl` | Create SSpec tests yourself |
| Detail design | `doc/05_design/<feature>.md` | Create detail design yourself |
| Implementation | `src/**/<feature>.spl` | Implement the feature |

**Never fail because a prior step wasn't done by another LLM. Just do it.**

---

## Available Tools

| Tool | Purpose |
|------|---------|
| **Simple MCP** | `bin/simple query workspace-symbols`, `references`, `hover` — codebase search |
| **Simple LSP MCP** | `bin/simple query definition`, `completions` — code navigation |
| **Context7 MCP** | External library documentation lookup |
| **Playwright CLI** | `npx playwright` — web scraping, browser automation, domain research |

---

## Step 1: Research

Check: `doc/01_research/local/<feature>.md` and `doc/01_research/domain/<feature>.md` exist?

If missing, do both:

### Local Research
- Search `src/` for related types, functions, modules, call chains (use Simple MCP + LSP MCP)
- Search `doc/` for prior research, design docs, ADRs
- Output: `doc/01_research/local/<feature>.md`

### Domain Research
- Web search via Playwright CLI for external knowledge, papers, prior art
- Output: `doc/01_research/domain/<feature>.md`

### Requirement Options
- Generate feature options with pros/cons/effort: `doc/02_requirements/feature/<feature>_options.md`
- Generate NFR options: `doc/02_requirements/nfr/<feature>_options.md`
- **Ask user** to select, then write final: `doc/02_requirements/feature/<feature>.md` and `doc/02_requirements/nfr/<feature>.md`

---

## Step 2: Design

Check: `doc/04_architecture/<feature>.md` and `doc/05_design/<feature>.md` exist?

If missing, do all:

### UI Design (if feature has UI)
- TUI mockups: `doc/05_design/<feature>_tui.md`
- GUI mockups: `doc/05_design/<feature>_gui.md`

### Architecture
- Evaluate patterns, apply MDSOC where appropriate
- Output: `doc/04_architecture/<feature>.md`

### System Test Design
- SSpec BDD tests: `doc/06_spec/app/<app_name>/feature/<feature>_spec.spl`
- Test plan: `doc/03_plan/sys_test/<feature>.md`
- Matchers (built-in only): `to_equal`, `to_be`, `to_be_nil`, `to_contain`, `to_start_with`, `to_end_with`, `to_be_greater_than`, `to_be_less_than`

### Detail Design
- Data structures, algorithms, module interactions, error handling
- Output: `doc/05_design/<feature>.md`
- Agent task breakdown: `doc/03_plan/agent_tasks/<feature>.md`

---

## Step 3: Implementation

See `/impl` skill (15-phase workflow). Key phases:
1. Implement in `src/**/<feature>.spl`
2. Unit + integration tests (80%+ coverage)
3. Doctest for public fns
4. Bug reports, duplication check, refactoring
5. Full test suite pass

---

## Step 4: Verify

Run `/verify` — production readiness check:

| Check | Fail Condition |
|-------|---------------|
| SSpec Tests | `pass_todo`, `expect(true).to_equal(true)`, empty bodies |
| Implementation | Stub functions, hardcoded returns, TODO-only bodies |
| Requirements | REQ-NNN without implementation or test coverage |
| NFR | Targets without verification mechanism |
| Architecture | `doc/04_architecture/` missing or outdated |
| Design | `doc/05_design/` missing or outdated |

Must show `STATUS: PASS` before release.

---

## Step 5: Release

Run `/release` — version bump, CHANGELOG, commit, tag, push.

---

## MCP Registry Distribution

MCP server available via npm: `@simple-lang/mcp-server`
- Package: `tools/mcp-registry/` (npm wrapper for native binary)
- Registry: `registry.modelcontextprotocol.io`
- Guide: `doc/07_guide/tooling/ai_cli_registration.md`

---

## Critical Rules

- **Self-sufficient**: never fail because another LLM didn't do its step — do it yourself
- NEVER overwrite another LLM's research — append and annotate
- All requirement options must include pros, cons, and effort estimate
- User MUST select requirements — never auto-select
- Unchosen options are DELETED, not archived

## Artifacts Summary

| Step | Artifact | Location |
|------|----------|----------|
| 1 | Local research | `doc/01_research/local/<feature>.md` |
| 1 | Domain research | `doc/01_research/domain/<feature>.md` |
| 1 | Feature requirements | `doc/02_requirements/feature/<feature>.md` |
| 1 | NFR requirements | `doc/02_requirements/nfr/<feature>.md` |
| 2 | Architecture | `doc/04_architecture/<feature>.md` |
| 2 | UI design | `doc/05_design/<feature>_tui.md`, `_gui.md` |
| 2 | Detail design | `doc/05_design/<feature>.md` |
| 2 | System tests | `doc/06_spec/app/<app_name>/feature/<feature>_spec.spl` |
| 2 | Test plan | `doc/03_plan/sys_test/<feature>.md` |
| 2 | Agent tasks | `doc/03_plan/agent_tasks/<feature>.md` |
| 3 | Source code | `src/**/<feature>.spl` |
| 4 | Verify report | Terminal output (PASS/FAIL/WARN) |
