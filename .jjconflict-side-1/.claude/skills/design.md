# Design Skill — Detail Design

## Prerequisites
| Artifact | Path | If missing |
|----------|------|-----------|
| Requirements | `doc/02_requirements/<domain>/<topic>/<feature>.md` | Run `/research` first |
| Architecture | `doc/04_architecture/<domain>/<topic>/<feature>.md` | Run `/arch` first |

## Workflow

1. Create detailed design: data structures, algorithms, module interactions, error handling
2. Output: `doc/05_design/<domain>/<topic>/<feature>.md`
3. Agent task breakdown: `doc/03_plan/agent_tasks/<feature>.md`

## Quality Check

1. Ask user: "Should design change?"
2. If yes, loop back

## Outputs
| Artifact | Location |
|----------|----------|
| Detail design | `doc/05_design/<domain>/<topic>/<feature>.md` |
| Agent tasks | `doc/03_plan/agent_tasks/<feature>.md` |

Broad-lane agent-task docs must list lower-model sidecar lanes or `N/A`, such
as Codex Spark, Claude Haiku, or Claude Sonnet for parallel exploration, plus
merge owner and final normal/highest-capability reviewer. Before those sidecars
start, the primary/best model defines the shared interface names, manual
`step("...")` flow helper names, setup/checker helper names, and placeholder
fail-fast helpers (`assert(false)` or `fail(...)`) that sidecars must target.
The final normal/highest-capability reviewer must accept the merged sidecar
design and generated-manual quality before implementation handoff.
If design changes workflow/tooling,
evidence wrappers, generated spec shape, or verification contracts, update the
matching `doc/07_guide`, `doc/06_spec`, `.codex/skills/`, `.agents/skills/`,
`.claude/skills/`, `.claude/agents/spipe/`, and `.gemini/commands/`
instructions before implementation handoff.

## Critical Rules

- Never design without approved architecture (`/arch`)
- If another LLM already created artifacts, review and extend — never overwrite
