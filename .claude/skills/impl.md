# Impl Skill — 15-Phase Implementation Workflow

**Purpose**: Full feature implementation lifecycle from requirements through VCS sync, with agent teams, BDD, duplication checks, and doc consistency.

---

## Phase Overview

| # | Phase | Agent | Output |
|---|-------|-------|--------|
| 1 | Requirements | main | `doc/plan/requirement/<feature>.md` |
| 2 | Research | research-team | `doc/research/<feature>.md` |
| 3 | Req Update | main | Updated `doc/plan/requirement/<feature>.md` |
| 4 | Plan + Design | design-team | `doc/plan/<feature>.md`, `doc/design/<feature>.md` |
| 5 | Model Selection | main | Task-to-model assignment |
| 6 | System Test (SSpec) | test-agent | `test/system/<feature>_spec.spl` |
| 7 | Doc Consistency | review-agent | Cross-ref validation |
| 8 | Implementation | code-team | `src/**/<feature>.spl` |
| 9 | Unit + IT Tests | test-agent | 80%+ branch coverage |
| 10 | Doctest | code-agent | `"""..."""` sdoctest for public fns |
| 11 | Bug Reports | review-agent | `doc/tracking/bug/<feature>_limitations.md` |
| 12 | Duplication Check | review-agent | jscpd + semantic check |
| 13 | Refactoring | code-agent | Files >800 lines split |
| 14 | Full Test Suite | test-agent | All tests pass |
| 15 | VCS Sync | main | Invoke `/git-jj-sync` |

---

## Agent Teams

```
research-team:  explore → docs          (sequential)
design-team:    explore → code → docs   (sequential)
code-team:      code → test             (sequential)
review-team:    explore → docs          (sequential)
```

Use `agent_team_create` + `agent_team_run` MCP tools, or spawn Task agents manually with the corresponding agent definitions from `.claude/agents/`.

---

## Phase Details

### Phase 1: Requirements

**Agent:** main

1. Create `doc/plan/requirement/<feature>.md` with:
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

1. Update `doc/plan/requirement/<feature>.md` based on research findings
2. If research revealed significant new concerns, re-suggest I/O examples
3. Get user approval on updated requirements

### Phase 4: Plan + Design

**Agent:** design-team (explore → code → docs)

1. Create `doc/plan/<feature>.md`:
   - Task breakdown with numbered items
   - Dependencies between tasks (DAG)
   - Difficulty rating per task (1-5 scale)
   - **Split any task rated ≥4** into smaller subtasks
2. Create `doc/design/<feature>.md`:
   - Module structure
   - Type definitions
   - API surface
   - Integration points with existing code

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
4. Use only built-in matchers: `to_equal`, `to_be`, `to_be_nil`, `to_contain`, `to_start_with`, `to_end_with`, `to_be_greater_than`, `to_be_less_than`
5. See `/sspec` skill for template and conventions

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
                  ↘ test/system/<f>_spec.spl
                  ↘ src/**/<f>.spl
```

### Phase 8: Implementation

**Agent:** code-team (code → test)

1. Implement in `src/**/<feature>.spl`
2. Follow `/coding` skill rules
3. **Minimize code size** — no over-engineering
4. **Stub Prevention Gate** (REQ-PREV-003 — mandatory before marking phase complete):
   a. Run `bin/simple build lint` on all touched files
   b. Grep for: `pass$`, `return 0$`, `return ""$`, `return nil$`, `return false$`, `return \[\]$`
   c. Verify no function ignores all its parameters (STUB001 = hard fail)
   d. Verify no function returns its input unchanged without `pass_do_nothing` or comment
   e. Every incomplete function MUST use `pass_todo("reason")` — never bare `pass`
5. Each agent runs duplication check on touched files after work

### Phase 9: Unit + Integration Tests

**Agent:** test-agent

1. Write unit tests alongside implementation
2. Write integration tests for module boundaries
3. Target: **80%+ branch coverage**
4. Run: `bin/simple test test/.../<feature>_spec.spl`

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
2. Output: `doc/tracking/bug/<feature>_limitations.md`
3. Each limitation includes: description, workaround, severity, related issue (if any)

### Phase 12: Duplication + Stub Check

**Agent:** review-agent

Three checks:

1. **Token duplication (jscpd)**: 5-line minimum, threshold ≤5%
   ```bash
   npx jscpd src/**/<feature>.spl --min-lines 5 --threshold 5
   ```

2. **Semantic duplication**: Cosine similarity threshold ≤0.85
   - Compare new functions against existing codebase
   - Flag near-duplicates for review

3. **Stub Scan** (REQ-PREV-004 — mandatory):
   a. Run `check_stub_impl()` on all new/modified declarations
   b. Verify every `pass_todo` has a non-empty reason message
   c. Report stub stats: count of pass_todo / pass_do_nothing / fully implemented
   d. Detect identity-return functions (`fn f(x): x`) without documentation (REQ-PREV-005)
   e. Any STUB001 warning = **hard fail**, loop back to Phase 8

If any check fails, refactor before proceeding.

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

1. Invoke `/git-jj-sync` workflow
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
| Requirement | doc/plan/requirement/<feature>.md |
| Research | doc/research/<feature>.md |
| Plan | doc/plan/<feature>.md |
| Design | doc/design/<feature>.md |
| System Tests | test/system/<feature>_spec.spl |
| Source | src/.../<feature>.spl |
| Unit Tests | test/.../<feature>_spec.spl |
| Bug Report | doc/tracking/bug/<feature>_limitations.md |

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

## Per-Agent Checks

Every agent must run after completing its work:

- `code`: compile + touched tests + duplication check + **stub scan** (STUB001 = hard fail)
- `test`: tests actually fail-first, coverage target met
- `review`: cross-ref consistency + **stub scan** (check_stub_impl on all new decls, verify pass_todo reasons)
- `main`: docs approved before moving phases + **verify stub stats** in completion report

## Stub Stats (Completion Report Addendum)

Add to the completion report:

```markdown
## Stub Prevention
- STUB001 warnings: 0 (must be zero)
- pass_todo count: N (each with reason)
- pass_do_nothing count: N (each intentional)
- Identity-return functions: N (each documented)
```
