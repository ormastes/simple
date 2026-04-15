# SStack Research Skill — Phase 2: Analyst

**Trigger:** `/sstack-research` or when a feature with `Phase: intake-done` needs codebase and domain research.

## What This Skill Does

Researches existing code and domain knowledge relevant to the refined goal. Identifies reusable modules, maps requirements to code areas, and appends findings to the state file.

## When to Use

- After Phase 1 (intake) completes with `Phase: intake-done`
- When you need to understand what code already exists before designing
- When domain knowledge gaps need to be filled

## Workflow

1. Read `.sstack/<feature>/state.md` — extract refined goal and acceptance criteria
2. Search the codebase for related code using Grep, Glob, Read
3. Identify reusable modules, functions, types, and patterns
4. Note any domain knowledge gaps; use WebSearch if needed
5. Draft a requirements summary derived from the ACs
6. Append findings to the state file (do not modify earlier sections)

## Tools

- **Grep** — find function signatures, type definitions, patterns
- **Glob** — locate files by name/path pattern
- **Read** — inspect specific files (targeted, not exploratory)
- **WebSearch** — domain knowledge only when codebase has no answer

## Boundaries (Boil a Small Lake)

- ONLY research and discovery
- Do NOT propose architecture or write code
- Do NOT create test files
- Do NOT sketch module boundaries
- Context budget: sub-40% — targeted searches only, no full-tree scans

## Entry Criteria

- `.sstack/<feature>/state.md` exists with `Phase: intake-done`
- Refined goal and acceptance criteria are present

## Exit Criteria

- State file contains `## Research Summary` with:
  - Existing code references (file paths + line ranges)
  - Reusable modules/functions identified
  - Domain knowledge notes (if any)
  - Open questions: NONE (all resolved, or escalated back to intake)
- State file contains `## Requirements` — derived from ACs, mapped to code areas
- `## Phase` updated to `research-done`

## State File Additions

```markdown
## Research Summary
### Existing Code
- `src/path/to/file.spl:42-60` — <what it does, why it's relevant>
- ...

### Reusable Modules
- `std.X` — <what it provides>
- ...

### Domain Notes
- <any external knowledge needed>

### Open Questions
- NONE

## Requirements
- REQ-1 (from AC-1): <requirement statement> — area: `src/path/`
- REQ-2 (from AC-2): <requirement statement> — area: `src/path/`
- ...

## Phase
research-done

## Log
- intake: Created state file with N acceptance criteria
- research: Found N reusable modules, N existing files, N requirements drafted
```

## Next Phase

Hand off to **sstack-arch** (Phase 3: Architect) once `Phase: research-done` is set.
