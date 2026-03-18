# Impl Skill — 17-Phase Implementation Workflow

**Purpose**: Full feature implementation lifecycle from requirements through VCS sync, with agent teams, BDD, duplication checks, codex verification, and gemini visual design.

---

## Phase Overview

| # | Phase | Agent | Output |
|---|-------|-------|--------|
| 1 | Requirements | main | `doc/requirement/<feature>.md` |
| 2 | Research | research-team | `doc/research/<feature>.md` |
| 3 | Req Update | main | Updated `doc/requirement/<feature>.md` |
| 4 | Plan + Design | design-team | `doc/plan/<feature>.md`, `doc/design/<feature>.md` |
| 4g | GUI/Visual Design | **gemini-designer** | Layout mockups, UI concepts, image assets |
| 4v | Plan Verification | **codex-verifier** | Verification report (status accuracy + achievability) |
| 5 | Model Selection | main | Task-to-model assignment |
| 6 | System Test (SSpec) | test-agent | `test/system/<feature>_spec.spl` |
| 6v | Test Verification | **codex-verifier** | Coverage + integrity report |
| 7 | Doc Consistency | review-agent | Cross-ref validation |
| 8 | Implementation | code-team | `src/**/<feature>.spl` |
| 9 | Unit + IT Tests | test-agent | 80%+ branch coverage |
| 10 | Doctest | code-agent | `"""..."""` sdoctest for public fns |
| 11 | Bug Reports | review-agent | `doc/bug/<feature>_limitations.md` |
| 12 | Duplication Check | review-agent | jscpd + semantic check |
| 13 | Refactoring | code-agent | Files >800 lines split |
| 14 | Full Test Suite | test-agent | All tests pass |
| 15 | VCS Sync | main | Invoke `/vcs` |

---

## Agent Teams

```
research-team:   explore → docs                    (sequential)
design-team:     explore → code → docs             (sequential)
code-team:       code → test                       (sequential)
review-team:     explore → docs                    (sequential)
```

### LLM Subagents (via llm_cli_tools agent worker)

| Subagent | Provider | Role | When Used |
|----------|----------|------|-----------|
| **codex-verifier** | `codex_api` | Verification: plan accuracy, test coverage, dummy detection | Phase 4v, 6v |
| **gemini-designer** | `gemini_api` | Visual design: UI layout, mockups, image concepts, GUI wireframes | Phase 4g, any visual update |

**Providers:** `codex_api` (OpenAI REST, recommended), `codex_cli` (CLI fallback), `gemini_api` (Gemini REST, recommended), `gemini_cli` (CLI fallback)

**Spawn command** (from `examples/llm_cli_tools/`):
```bash
# Codex verifier (API — recommended)
AGENT_CMD=spawn AGENT_PROVIDER=codex_api AGENT_ROLE=verify \
  AGENT_SYSTEM="You are a plan verification agent..." \
  AGENT_PROMPT_FILE=doc/plan/<feature>.md \
  ../../bin/release/simple run src/app/agent/orchestrator.spl

# Gemini designer (API — recommended)
AGENT_CMD=spawn AGENT_PROVIDER=gemini_api AGENT_ROLE=design \
  AGENT_SYSTEM="You are a UI/visual design agent..." \
  AGENT_PROMPT_FILE=doc/design/<feature>.md \
  ../../bin/release/simple run src/app/agent/orchestrator.spl
```

Use `agent_team_create` + `agent_team_run` MCP tools, or spawn Task agents manually with the corresponding agent definitions from `.claude/agents/`.

---

## Phase Details

### Phase 1: Requirements

**Agent:** main

1. Create `doc/requirement/<feature>.md` with:
   - Feature name and motivation (why)
   - Scope (what's in, what's out)
   - I/O examples — suggest 3-5 examples, let user choose
   - Acceptance criteria
   - Dependencies on existing modules
2. Present to user for approval before proceeding

### Phase 2: Research

**Agent:** research-team (explore → docs)

1. **Codebase research**: Find related modules, existing patterns, potential conflicts
2. **Web research** (if needed): Similar implementations, best practices
3. Output: `doc/research/<feature>.md` with findings, recommendations, risks

### Phase 3: Req Update

**Agent:** main

1. Update `doc/requirement/<feature>.md` based on research findings
2. If research revealed significant new concerns, re-suggest I/O examples
3. Get user approval on updated requirements

### Phase 4: Plan + Design

**Agent:** design-team (explore → code → docs)

1. Create `doc/plan/<feature>.md` with **standardized header**:

```markdown
# <Feature> — Plan

## Objective
What this achieves (1-3 sentences).

## Current Status
| Component | Status | Evidence |
|-----------|--------|----------|
| module_x  | Real   | test/unit/module_x_spec.spl passes |
| module_y  | Dummy (pass_todo) | src/module_y.spl:42 |
| module_z  | Fallback to other module | uses module_w instead |

## What To Do
1. Task description (difficulty: N)...
2. Task description (difficulty: N)...
```

   - Task breakdown with numbered items
   - Dependencies between tasks (DAG)
   - Difficulty rating per task (1-5 scale)
   - **Split any task rated ≥4** into smaller subtasks

2. Create `doc/design/<feature>.md`:
   - Module structure
   - Type definitions
   - API surface
   - Integration points with existing code

### Phase 4g: GUI/Visual Design (conditional)

**Agent:** gemini-designer (LLM subagent)
**When:** Feature involves UI, TUI, GUI, images, visual layout, or any graphical component.
**Skip:** Pure backend/compiler/library features with no visual component.

Gemini receives the design doc and produces:

1. **Layout mockups** — ASCII wireframes or textual UI descriptions
2. **Visual concepts** — Color schemes, component hierarchy, interaction flow
3. **Image asset descriptions** — If icons, logos, or graphics are needed
4. **TUI panel layout** — For terminal-based interfaces (box drawing, panel arrangement)
5. **Accessibility notes** — Keyboard navigation, screen reader considerations

**Gemini prompt template:**
```
You are a UI/visual design agent for the Simple language project.
Given the design document, produce:
1. ASCII wireframe of the main interface layout
2. Component hierarchy (which panels contain what)
3. Color scheme recommendations (ANSI terminal colors for TUI, or CSS for web)
4. Interaction flow (key bindings, mouse events, navigation)
5. Responsive behavior (narrow terminal, small window)

Design doc:
<contents of doc/design/<feature>.md>
```

**Output:** Appended to `doc/design/<feature>.md` under `## Visual Design` section, or as separate `doc/design/<feature>_visual.md`.

### Phase 4v: Plan Verification

**Agent:** codex-verifier (LLM subagent)
**Always runs** after Phase 4 completes.

Codex receives the plan doc and verifies:

1. **Current status accuracy:**
   - For each component listed as "Real": verify source file exists and has **no** `pass_todo`, `pass_do_nothing`, or placeholder implementations
   - For each component listed as "Done": verify tests exist and reference the module
   - **Flag** any component with dummy/temp/fallback that claims to be "Real"
   - **Flag** any component that delegates to another module differently than designed

2. **Objective achievability:**
   - Check that the listed to-do tasks, if all completed, would satisfy the stated objective
   - Flag missing prerequisite tasks or unreachable goals
   - Flag tasks that depend on unimplemented infrastructure

**Codex prompt template:**
```
You are a plan verification agent. Given a plan document, verify:
1. CURRENT STATUS: For each component marked "Real" or "Done", check if the source
   file exists and contains no pass_todo, pass_do_nothing, or placeholder stubs.
   Report any component where status is inaccurate.
2. ACHIEVABILITY: Check if completing all listed tasks would achieve the stated
   objective. Report any missing prerequisites or impossible goals.

Output format:
STATUS_CHECK:
  - component_name: PASS/FAIL (reason)
ACHIEVABILITY_CHECK:
  - PASS/FAIL (reason)
OVERALL: PASS/FAIL

Plan doc:
<contents of doc/plan/<feature>.md>
```

**If FAIL:** Loop back to Phase 4 to fix the plan before proceeding.

### Phase 5: Model Selection

**Agent:** main

Assign model per task based on difficulty:

| Difficulty | Model | Use For |
|-----------|-------|---------|
| 1-2 | haiku | Boilerplate, simple wiring, test scaffolding |
| 3 | sonnet | Standard features, moderate logic |
| 4-5 | opus | Complex algorithms, type system work, compiler passes |

### Phase 6: System Test (SSpec)

**Agent:** test-agent

1. Create `test/system/<feature>_spec.spl` using SSpec BDD format
2. Tests MUST assert-fail-first (write tests before implementation)
3. Tests are doc-driven — each test traces to a requirement
4. Add cross-reference tags:
   ```simple
   # @req REQ-042
   # @feature feature_name
   tag: slow, system

   describe "Feature Name":
       # @scenario SC-001
       it "does the main thing":
           ...
   ```
5. Use only built-in matchers: `to_equal`, `to_be`, `to_be_nil`, `to_contain`, `to_start_with`, `to_end_with`, `to_be_greater_than`, `to_be_less_than`
6. See `/test` skill for template and conventions

### Phase 6v: Test Verification

**Agent:** codex-verifier (LLM subagent)
**Always runs** after Phase 6 completes.

Codex checks:

1. **Document existence:**
   - `doc/requirement/<feature>.md` exists
   - `doc/research/<feature>.md` exists (or Phase 2 was skipped with approval)
   - `doc/plan/<feature>.md` exists with standardized header
   - `test/system/<feature>_spec.spl` exists

2. **SSpec scenario coverage:**
   - System test covers **all acceptance criteria** from requirement doc
   - Each `it` block tests a meaningful scenario (not trivial pass-through)
   - Cases that **cannot** be system-tested are documented for integration test with mock

3. **Test integrity:**
   - System test path has **NO mock or dummy implementations**
   - Mock-based tests belong in `test/integration/` not `test/system/`
   - System test file has `# @req` cross-reference tag

4. **Coverage plan:**
   - Implementation modules planned for **≥80% branch coverage** with unit tests
   - Unit/integration tests reference parent system test: `# @parent test/system/<feature>_spec.spl`

**Codex prompt template:**
```
You are a test verification agent. Given the requirement doc and system test file, verify:
1. DOCUMENTS: requirement, research, plan all exist
2. COVERAGE: every acceptance criterion has a matching it() block
3. INTEGRITY: no mock/dummy in system test path, proper @req tags
4. PLAN: unit test coverage target >= 80%

Output format:
DOC_CHECK:
  - requirement.md: EXISTS/MISSING
  - research.md: EXISTS/MISSING/SKIPPED
  - plan.md: EXISTS/MISSING
  - system_spec.spl: EXISTS/MISSING
COVERAGE_CHECK:
  - criterion_1: COVERED by "it block name" / UNCOVERED
INTEGRITY_CHECK:
  - mocks_in_system_test: NONE/FOUND (list)
  - req_tag_present: YES/NO
OVERALL: PASS/FAIL

Requirement doc:
<contents>

System test:
<contents>
```

**If FAIL:** Loop back to Phase 6 to fix tests before proceeding.

### Phase 7: Doc Consistency

**Agent:** review-agent

Check all documents created so far:

1. **Cross-references**: Every doc links to related docs bidirectionally
2. **Terminology**: Same terms used consistently across all docs
3. **REQ-ID tracing**: Each requirement has an ID, traced through plan → design → test
4. **Rewrite** any inconsistencies until all docs are coherent

### Cross-Reference Map

All documents link bidirectionally:

```
requirement/<f>.md ↔ plan/<f>.md ↔ design/<f>.md ↔ research/<f>.md
                  ↘ test/system/<f>_spec.spl    (# @req REQ-NNN)
                  ↘ src/**/<f>.spl
                  ↘ test/unit/**/<f>_spec.spl   (# @parent test/system/...)
                  ↘ test/integration/**/<f>_spec.spl (# @parent test/system/...)
```

### Phase 8: Implementation

**Agent:** code-team (code → test)

1. Implement in `src/**/<feature>.spl`
2. Follow `/coding` skill rules
3. **Minimize code size** — no over-engineering
4. **Detect dummy implementations**: grep for bare `pass$`, empty fn bodies
5. Each agent runs duplication check on touched files after work

### Phase 9: Unit + Integration Tests

**Agent:** test-agent

1. Write unit tests alongside implementation
2. Write integration tests for module boundaries
3. Target: **80%+ branch coverage**
4. Add cross-reference tags:
   ```simple
   # @parent test/system/<feature>_spec.spl
   # @req REQ-042
   ```
5. Run: `bin/simple test test/.../<feature>_spec.spl`

### Phase 10: Doctest

**Agent:** code-agent

Add sdoctest to every public function:

```simple
fn square(x: i64) -> i64:
    """
    Returns the square of x.

    sdoctest:
        expect(square(3)).to_equal(9)
        expect(square(-2)).to_equal(4)
    """
    x * x
```

### Phase 11: Bug Reports

**Agent:** review-agent

1. Document any workarounds discovered during implementation
2. Output: `doc/bug/<feature>_limitations.md`
3. Each limitation includes: description, workaround, severity, related issue (if any)

### Phase 12: Duplication Check

**Agent:** review-agent

Two checks:

1. **Token duplication (jscpd)**: 5-line minimum, threshold ≤5%
   ```bash
   npx jscpd src/**/<feature>.spl --min-lines 5 --threshold 5
   ```

2. **Semantic duplication**: Cosine similarity threshold ≤0.85
   - Compare new functions against existing codebase
   - Flag near-duplicates for review

If either check fails, refactor before proceeding.

### Phase 13: Refactoring

**Agent:** code-agent

1. Any file >800 lines → split into meaningful modules
2. Extract shared logic if duplication check flagged issues
3. Ensure imports and module structure remain clean

### Phase 14: Full Test Suite

**Agent:** test-agent

```bash
bin/simple test                    # All tests (except slow)
bin/simple build lint              # Linter clean
bin/simple build check             # All checks pass
```

All tests must pass before proceeding to Phase 15. If failures occur, loop back to Phase 8 (implementation) to fix.

### Phase 15: VCS Sync

**Agent:** main

1. Invoke `/vcs` workflow
2. Generate completion report: `doc/report/<feature>_complete_<date>.md`

---

## Completion Report

Generated at `doc/report/<feature>_complete_<YYYY-MM-DD>.md`:

```markdown
# <Feature> — Implementation Complete

**Date:** <YYYY-MM-DD>
**Phases completed:** 1-15

## Artifacts

| Type | Path |
|------|------|
| Requirement | doc/requirement/<feature>.md |
| Research | doc/research/<feature>.md |
| Plan | doc/plan/<feature>.md |
| Design | doc/design/<feature>.md |
| System Tests | test/system/<feature>_spec.spl |
| Source | src/.../<feature>.spl |
| Unit Tests | test/.../<feature>_spec.spl |
| Bug Report | doc/bug/<feature>_limitations.md |

## Verification Results
- Plan verification (codex): PASS/FAIL
- Test verification (codex): PASS/FAIL
- Visual design (gemini): PASS/SKIPPED

## Test Results
- Total: X passed, Y failed
- Coverage: Z%

## Duplication
- Token (jscpd): X%
- Semantic max similarity: 0.XX

## Limitations Found
- <list from Phase 11>
```

---

## LLM Subagent Details

### Codex Verifier

**Provider:** `codex_api` (OpenAI REST API — recommended) or `codex_cli` (CLI fallback)
**Binary:** `curl` (API) or `codex` (CLI)
**Model:** `o3-mini` (API mode)
**Env:** `OPENAI_API_KEY` must be set for API mode
**Role:** Automated verification — never writes code, only reports findings.

**Used in:**
- Phase 4v: Verify plan current-status is real (not dummy/fallback)
- Phase 6v: Verify system test coverage and integrity

**Spawn from `examples/llm_cli_tools/`:**
```bash
# API mode (recommended)
AGENT_CMD=spawn AGENT_PROVIDER=codex_api AGENT_ROLE=verify \
  AGENT_SYSTEM="You are a verification agent. Check for accuracy, do not modify files." \
  AGENT_PROMPT_FILE=<path_to_verify> \
  ../../bin/release/simple run src/app/agent/orchestrator.spl

# CLI fallback
AGENT_CMD=spawn AGENT_PROVIDER=codex_cli AGENT_ROLE=verify \
  AGENT_SYSTEM="You are a verification agent. Check for accuracy, do not modify files." \
  AGENT_PROMPT_FILE=<path_to_verify> \
  ../../bin/release/simple run src/app/agent/orchestrator.spl
```

**Result:** Read via `AGENT_CMD=result AGENT_ID=<id> ... orchestrator.spl`
**Logs:** `data/agents/logs/<agent_id>.log`

### Gemini Designer

**Provider:** `gemini_api` (Google Gemini REST API — recommended) or `gemini_cli` (CLI fallback)
**Binary:** `curl` (API) or `gemini` (CLI)
**Model:** `gemini-2.0-flash` (API mode)
**Env:** `GEMINI_API_KEY` must be set for API mode
**Role:** Visual/UI design — produces layout mockups, wireframes, visual concepts.

**Used in:**
- Phase 4g: GUI/TUI/visual design when feature has UI component
- Any phase where visual updates are needed (on-demand)

**Triggers** (when to invoke gemini-designer):
- Feature mentions: UI, TUI, GUI, dashboard, panel, layout, widget, screen, window, dialog
- Feature mentions: image, icon, logo, graphic, visual, color, theme, style
- Design doc includes visual components
- User explicitly requests visual design

**Spawn from `examples/llm_cli_tools/`:**
```bash
# API mode (recommended)
AGENT_CMD=spawn AGENT_PROVIDER=gemini_api AGENT_ROLE=design \
  AGENT_SYSTEM="You are a UI/visual design agent. Produce ASCII wireframes, layout specs, and visual concepts." \
  AGENT_PROMPT_FILE=doc/design/<feature>.md \
  ../../bin/release/simple run src/app/agent/orchestrator.spl

# CLI fallback
AGENT_CMD=spawn AGENT_PROVIDER=gemini_cli AGENT_ROLE=design \
  AGENT_SYSTEM="You are a UI/visual design agent. Produce ASCII wireframes, layout specs, and visual concepts." \
  AGENT_PROMPT_FILE=doc/design/<feature>.md \
  ../../bin/release/simple run src/app/agent/orchestrator.spl
```

---

## Per-Agent Checks

Every agent must run after completing its work:

1. **Duplication check** on touched files
2. **Lint check**: `bin/simple build lint`
3. **Test run** on relevant test files

Main agent additionally checks:

1. **No dummy implementations**: Search for bare `pass$`, empty fn bodies, `pass_todo` without a plan
2. **All tests pass** (except `--only-slow`)
3. **Doc cross-references** resolve correctly

---

## Skipping Phases

Some phases may be skipped with user approval:

- **Phase 2 (Research)**: Skip if feature is well-understood and isolated
- **Phase 4g (GUI Design)**: Skip if no visual component (auto-skipped)
- **Phase 10 (Doctest)**: Skip for internal/private modules
- **Phase 12 (Duplication)**: Skip for small changes (<50 lines)

Always ask user before skipping. Never skip Phases 1, 4v, 6, 6v, 8, 14, 15.

---

## Resuming Mid-Workflow

If a conversation ends mid-workflow:

1. Check which phases are complete by looking for artifacts (docs, tests, source)
2. Resume from the next incomplete phase
3. Re-validate previous phase outputs if significant time has passed

---

**Use this skill**: `/impl` or `cat .claude/skills/impl.md`
