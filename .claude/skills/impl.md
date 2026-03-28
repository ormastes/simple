# Impl Skill -- 15-Phase Implementation Workflow

## Phase Overview

| # | Phase | Agent | Output |
|---|-------|-------|--------|
| 1 | Requirements | main | `doc/plan/requirement/<feature>.md` |
| 2 | Research | research-team | `doc/research/<feature>.md` |
| 3 | Req Update | main | Updated requirement doc |
| 4 | Plan + Design | design-team | `doc/plan/<feature>.md`, `doc/design/<feature>.md` |
| 5 | Model Selection | main | Task-to-model assignment |
| 6 | System Test | test-agent | `test/system/<feature>_spec.spl` |
| 7 | Doc Consistency | review-agent | Cross-ref validation |
| 8 | Implementation | code-team | `src/**/<feature>.spl` |
| 9 | Unit + IT Tests | test-agent | 80%+ branch coverage |
| 10 | Doctest | code-agent | `"""..."""` sdoctest for public fns |
| 11 | Bug Reports | review-agent | `doc/tracking/bug/<feature>_limitations.md` |
| 12 | Duplication Check | review-agent | jscpd + semantic + stub scan |
| 13 | Refactoring | code-agent | Files >800 lines split |
| 14 | Full Test Suite | test-agent | All tests pass |
| 15 | VCS Sync | main | `/git-jj-sync` + completion report |

## Agent Teams

```
research-team:  explore -> docs          (sequential)
design-team:    explore -> code -> docs  (sequential)
code-team:      code -> test             (sequential)
review-team:    explore -> docs          (sequential)
```

## Phase Details

### Phase 1-3: Requirements + Research
1. Create `doc/plan/requirement/<feature>.md` (motivation, scope, I/O examples, acceptance criteria)
2. Research: codebase + web -> `doc/research/<feature>.md`
3. Update requirement doc based on research; get user approval

### Phase 4-5: Plan + Design + Model Selection
1. `doc/plan/<feature>.md`: task breakdown, deps DAG, difficulty 1-5 (split tasks >= 4)
2. `doc/design/<feature>.md`: module structure, types, API, integration points
3. Assign model: difficulty 1=haiku, 2=sonnet, 3-5=opus

### Phase 6-7: System Test + Doc Consistency
1. Create `test/system/<feature>_spec.spl` (SSpec BDD, fail-first). See `/sspec`
2. Cross-ref: bidirectional links, consistent terminology, REQ-ID tracing

### Phase 8: Implementation
1. Implement in `src/**/<feature>.spl`, follow `/coding` rules
2. **Stub Prevention Gate** (mandatory):
   - `bin/simple build lint` on touched files
   - `bin/simple query workspace-symbols --query pass_todo` to find stubs
   - No function ignoring all params (STUB001 = hard fail)
   - Every incomplete fn MUST use `pass_todo("reason")`

### Phase 9-10: Tests + Doctest
1. Unit + integration tests, target 80%+ branch coverage
2. Add sdoctest to every public fn: `""" sdoctest: expect(...).to_equal(...) """`

### Phase 11-13: Bug Reports + Duplication + Refactoring
1. Document workarounds in `doc/tracking/bug/<feature>_limitations.md`
2. Duplication: `bin/simple duplicate-check <dir>` (token + cosine + semantic)
3. Stub scan: verify pass_todo reasons, detect identity-returns (STUB001 = hard fail -> loop to Phase 8)
4. Split files >800 lines

### Phase 14-15: Full Test Suite + VCS Sync
```bash
bin/simple test && bin/simple build lint && bin/simple build check
```
All pass -> `/git-jj-sync` -> `doc/report/<feature>_complete_<date>.md`

## Per-Agent Checks

- **code**: compile + tests + duplication + stub scan (STUB001 = hard fail)
- **test**: fail-first verification, coverage target met
- **review**: cross-ref consistency + stub scan on all new decls
- **main**: docs approved before moving phases, verify stub stats in completion report
