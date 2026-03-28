# Gemini Agent — Self-Sufficient Feature Pipeline

**Full pipeline (ideal):** `/research` -> `/design` -> `/impl` -> `/verify` -> `/release`

Each step is **self-sufficient** — if prior steps were not done (by Claude, Codex, or anyone), do them yourself before proceeding.

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

## Step 1: Research

Check: `doc/01_research/local/<feature>.md` and `doc/01_research/domain/<feature>.md` exist?

If missing, do both:

### Local Research
- Search `src/` for related types, functions, modules, call chains
- Search `doc/` for prior research, design docs, ADRs
- Output: `doc/01_research/local/<feature>.md`

### Domain Research
- Web search for external knowledge, papers, prior art
- Output: `doc/01_research/domain/<feature>.md`

### Requirement Options
- Generate feature options with pros/cons/effort: `doc/02_requirements/feature/<feature>_options.md`
- Generate NFR options: `doc/02_requirements/nfr/<feature>_options.md`
- **Ask user** to select, then write final: `doc/02_requirements/feature/<feature>.md` and `doc/02_requirements/nfr/<feature>.md`

---

## Step 2: Design

Check: `doc/04_architecture/<feature>.md` and `doc/05_design/<feature>.md` exist?

If missing, do all:

### UI Design (primary Gemini strength)
- TUI mockups with box-drawing characters, ANSI color annotations: `doc/05_design/<feature>_tui.md`
- GUI mockups with web patterns, responsive layout: `doc/05_design/<feature>_gui.md`
- Present component lists to user for confirmation

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

Implement in `src/**/<feature>.spl`:
1. Follow coding standards (`.spl` files only, generics with `<>`, no inheritance)
2. Unit + integration tests (80%+ coverage)
3. Doctest for public fns
4. Full test suite pass: `bin/simple test && bin/simple build lint`

---

## Step 4: Verify

Production readiness check:

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

Version bump, CHANGELOG update, commit, tag, push.

---

## Critical Rules

- **Self-sufficient**: never fail because another LLM didn't do its step — do it yourself
- NEVER overwrite another LLM's research — append and annotate
- All requirement options must include pros, cons, and effort estimate
- User MUST select requirements — never auto-select
- All code in `.spl` — no Python, no Bash (except 3 bootstrap scripts)
- SSpec matchers: built-in only (`to_equal`, `to_be`, `to_be_nil`, `to_contain`, etc.)

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
| 3 | Source code | `src/**/<feature>.spl` |
| 4 | Verify report | Terminal output (PASS/FAIL/WARN) |
