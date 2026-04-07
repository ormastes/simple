# Dev Skill — SStack Quick Profile

`/dev` is a **lightweight sstack profile** for everyday tasks. It runs the same SStack pipeline
but with merged/skipped phases for speed. Under the hood, it uses the same state file, quality
gates, and SSpec integration as full `/sstack`.

## Usage

```
/dev <description of what to build or fix>
```

Equivalent to: `/sstack --profile quick <description>`

Argument: `$ARGUMENTS`

## When to Use /dev vs Others

| Scenario | Use |
|----------|-----|
| Quick bug fix, small feature, TODO item, refactor | `/dev` (sstack quick profile) |
| Large feature needing full BDD/TDD cycle | `/sstack` (full 8-phase profile) |
| Large feature needing requirements + architecture docs | `/impl` (15 phases) |
| Research only, no implementation | `/research` |
| Design only, implementation later | `/design` |
| Post-implementation verification audit | `/verify` |

## Profile: Quick (5 phases mapped to SStack)

The quick profile merges and skips SStack phases for smaller tasks:

| Quick # | Quick Phase | SStack Phases | What |
|---------|-------------|---------------|------|
| 1 | Research | 1-dev + 2-research | Inline: refine goal + local scan |
| 2 | Plan | 3-arch + 4-spec | Combined arch + design + test plan, confirm with user |
| 3 | Implement | 5-implement | Code + tests together, stub gate |
| 4 | Verify | 6-refactor + 7-verify | Lint + test suite + quality check |
| 5 | Sync | 8-ship | jj commit |

**Key difference from full sstack:**
- Phases 1-2 run **inline** (no spawned agent) — saves context budget
- Phases 3-5 can run inline or spawned depending on complexity
- No separate refactor phase — folded into verify
- No separate spec-first phase — tests written alongside code

## Orchestrator Procedure

### Step 0: Setup

Same as sstack: derive `<feature>` slug, create `.sstack/<feature>/state.md` with the standard template.
Add `profile: quick` to the state file header.

### Phase 1: Research (inline — maps to sstack 1-dev + 2-research)

1. Parse user request, categorize task type: `feature`, `bug`, `todo`, `code-quality`
2. Refine into a clear, actionable, testable goal with 3-5 ACs
3. Search `src/` and `doc/` for related code using MCP tools:
   - `bin/simple query workspace-symbols` for type/function discovery
   - `bin/simple query references` for usage patterns
4. Check `doc/01_research/` for prior research
5. Write refined goal, ACs, and research summary to state file
6. Mark `1-dev` and `2-research` done in state file checklist
7. **Ask user to confirm** goal and ACs before proceeding
8. **Escalation:** If extensive research needed, suggest full `/sstack` or `/research` first

### Phase 2: Plan (inline — maps to sstack 3-arch + 4-spec)

1. Based on research, outline:
   - Affected modules and files
   - New types, functions, or modifications
   - Error handling strategy
   - Test strategy (unit, SSpec, or both)
2. Present plan to user — **wait for confirmation**
3. Write architecture and test plan to state file
4. Mark `3-arch` and `4-spec` done in state file checklist
5. **Escalation:** If plan reveals 3+ modules or new architecture, suggest full `/sstack` or `/impl`

### Phase 3: Implement (maps to sstack 5-implement)

1. Implement following `/coding` rules (read `.claude/skills/lib/coding.md`)
2. Write tests alongside code:
   - Unit tests for new functions
   - SSpec BDD tests if feature-level (see `/sspec`)
   - Add sdoctest to public functions: `""" sdoctest: expect(...).to_equal(...) """`
3. **Stub Prevention Gate** (mandatory — same as sstack):
   - `bin/simple build lint` on touched files
   - `bin/simple query workspace-symbols --query pass_todo` to find stubs
   - No function ignoring all params (STUB001 = hard fail)
   - Every incomplete fn MUST use `pass_todo("reason")`
4. If tests fail, fix before proceeding (max 5 iterations)
5. Mark `5-implement` done in state file checklist

### Phase 4: Verify (maps to sstack 6-refactor + 7-verify)

1. Run full checks:
   ```bash
   bin/simple test && bin/simple build lint && bin/simple build check
   ```
2. Quick stub scan on all new/changed files
3. Quick duplication check: `bin/simple duplicate-check <dir> --min-lines 5`
4. Verify each AC from state file against actual implementation
5. Mark ACs as checked, mark `6-refactor` and `7-verify` done
6. If failures: return to Phase 3 to fix
7. **Escalation:** If major quality issues found, suggest `/refactor` or full `/verify`

### Phase 5: Sync (maps to sstack 8-ship)

1. Commit via jj: `jj commit -m "<type>(<scope>): <description>"`
2. Commit types: `feat`, `fix`, `refactor`, `docs`, `test`, `chore`, `perf`, `build`
3. File count safety check (per `/sync` rules)
4. Write final summary to state file, mark `8-ship` done
5. Push only if user explicitly requests

### Completion

Same as sstack: report refined goal, all ACs checked, phase summary.

## Rules

- Uses the **same state file format** as full sstack (`.sstack/<feature>/state.md`)
- Uses the **same quality gates** — stub prevention, AC verification, exit criteria
- Uses the **same SSpec integration** for test-driven development
- Reuses sstack agent definitions by reference (not by spawning separate orchestrators)
- If the task grows beyond medium complexity during any phase, recommend switching to full `/sstack` or `/impl`
- Follow all rules from CLAUDE.md (jj VCS, .spl files only, no inheritance, etc.)
