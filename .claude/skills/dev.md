# Dev Skill — Streamlined 5-Phase Development Workflow

Lightweight full-cycle dev workflow for everyday tasks: research, plan, implement, verify, sync.
Runs inline in a single session — no state files, no spawned orchestrators.

## Usage

```
/dev <description of what to build or fix>
```

Argument: `$ARGUMENTS`

## When to Use /dev vs Others

| Scenario | Use |
|----------|-----|
| Quick bug fix, small feature, TODO item, refactor | `/dev` |
| Large feature needing requirements + architecture docs | `/impl` (15 phases) |
| Context-budget-sensitive or multi-agent orchestration | `/sstack` (8 phases) |
| Research only, no implementation | `/research` |
| Design only, implementation later | `/design` |
| Post-implementation verification audit | `/verify` |

## Phase Overview

| # | Phase | What | Output |
|---|-------|------|--------|
| 1 | Research | Local scan + optional domain search | Mental model |
| 2 | Plan | Combined arch + design, confirm with user | Inline plan |
| 3 | Implement | Code + tests together, stub gate | `src/**`, `test/**` |
| 4 | Verify | Test suite + lint + quality check | All green |
| 5 | Sync | jj commit | Committed change |

## Phase Details

### Phase 1: Research

1. Search `src/` and `doc/` for related code using MCP tools:
   - `bin/simple query workspace-symbols` for type/function discovery
   - `bin/simple query references` for usage patterns
   - `bin/simple query hover` for type info
2. Check `doc/01_research/` for prior research on this topic
3. Optionally web search for external context if the domain is unfamiliar
4. Summarize findings inline — no mandatory doc artifact
5. **Escalation:** If extensive research is needed (new domain, many unknowns), suggest `/research` first

### Phase 2: Plan

1. Based on research, outline:
   - Affected modules and files
   - New types, functions, or modifications
   - Error handling strategy
   - Test strategy (unit, SSpec, or both)
2. Present plan to user — **wait for confirmation before implementing**
3. **Escalation:** If plan reveals 3+ modules or new architecture, suggest `/impl` or `/sstack`
4. No separate doc artifacts unless user requests them

### Phase 3: Implement

1. Implement following `/coding` rules (read `.claude/skills/lib/coding.md`)
2. Write tests alongside code:
   - Unit tests for new functions
   - SSpec BDD tests if feature-level (see `/sspec`)
   - Add sdoctest to public functions: `""" sdoctest: expect(...).to_equal(...) """`
3. **Stub Prevention Gate** (mandatory):
   - `bin/simple build lint` on touched files
   - `bin/simple query workspace-symbols --query pass_todo` to find stubs
   - No function ignoring all params (STUB001 = hard fail)
   - Every incomplete fn MUST use `pass_todo("reason")`
4. If tests fail, fix before proceeding (max 5 iterations)

### Phase 4: Verify

1. Run full checks:
   ```bash
   bin/simple test && bin/simple build lint && bin/simple build check
   ```
2. Quick stub scan on all new/changed files
3. Quick duplication check: `bin/simple duplicate-check <dir> --min-lines 5`
4. If failures: return to Phase 3 to fix
5. **Escalation:** If major quality issues found, suggest `/refactor` or full `/verify`

### Phase 5: Sync

1. Commit via jj: `jj commit -m "<type>(<scope>): <description>"`
2. Commit types: `feat`, `fix`, `refactor`, `docs`, `test`, `chore`, `perf`, `build`
3. File count safety check (per `/sync` rules)
4. Push only if user explicitly requests: `jj bookmark set main -r @- && jj git push --bookmark main`

## Rules

- Runs inline in a single session — no state files, no spawned orchestrators
- Reuses existing skill patterns by reference, not by spawning them
- If the task grows beyond medium complexity during any phase, recommend switching to `/impl` or `/sstack`
- Stub Prevention Gate in Phase 3 is mandatory — same STUB001 hard-fail rule as `/impl`
- Always confirm the plan with the user in Phase 2 before implementing
- Follow all rules from CLAUDE.md (jj VCS, .spl files only, no inheritance, etc.)
