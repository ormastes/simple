# Design Skill — Detail Design

## Prerequisites
| Artifact | Path | If missing |
|----------|------|-----------|
| Requirements | `doc/02_requirements/<domain>/<topic>/<feature>.md` | Run `/research` first |
| Architecture | `doc/04_architecture/<domain>/<topic>/<feature>.md` | Run `/arch` first |

## Workflow

1. For broad plans, merge lower-model sidecar findings when available (Codex
   Spark, Claude Haiku, or Claude Sonnet), then run this pass as the
   normal/highest-capability review before accepting broad design claims.
2. Define shared interface names and manual-facing setup/checker helper names
   before specs or implementation are accepted. Placeholder helpers must fail
   explicitly (`assert(false)` or equivalent).
3. Create detailed design: data structures, algorithms, module interactions, error handling
4. Output: `doc/05_design/<domain>/<topic>/<feature>.md`
5. Agent task breakdown: `doc/03_plan/<domain>/<topic>/<feature>.md`

## Quality Check

1. Ask user: "Should design change?"
2. Confirm matching `doc/07_guide`, `doc/06_spec`, `.codex/skills/`,
   `.agents/skills/`, `.claude/skills/`, and `.claude/agents/spipe/`
   process docs were updated when the workflow or tool contract changed
3. If yes, loop back

## Outputs
| Artifact | Location |
|----------|----------|
| Detail design | `doc/05_design/<domain>/<topic>/<feature>.md` |
| Agent tasks | `doc/03_plan/<domain>/<topic>/<feature>.md` |

Broad-lane agent-task docs must list lower-model sidecar lanes or `N/A`, merge
owner, final normal/highest-capability reviewer, and the shared
interface/manual helper names accepted before implementation.

## Critical Rules

- Never design without approved architecture (`/arch`)
- If another LLM already created artifacts, review and extend — never overwrite
