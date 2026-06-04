# Design Skill — Detail Design

## Prerequisites
| Artifact | Path | If missing |
|----------|------|-----------|
| Requirements | `doc/02_requirements/<domain>/<topic>/<feature>.md` | Run `/research` first |
| Architecture | `doc/04_architecture/<domain>/<topic>/<feature>.md` | Run `/arch` first |

## Workflow

1. Create detailed design: data structures, algorithms, module interactions, error handling
2. Output: `doc/05_design/<domain>/<topic>/<feature>.md`
3. Agent task breakdown: `doc/03_plan/<domain>/<topic>/<feature>.md`

## Quality Check

1. Ask user: "Should design change?"
2. If yes, loop back

## Outputs
| Artifact | Location |
|----------|----------|
| Detail design | `doc/05_design/<domain>/<topic>/<feature>.md` |
| Agent tasks | `doc/03_plan/<domain>/<topic>/<feature>.md` |

## Critical Rules

- Never design without approved architecture (`/arch`)
- If another LLM already created artifacts, review and extend — never overwrite
