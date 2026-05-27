---
name: dev
description: Alias for /sstack — the 8-phase development orchestrator. Use for any dev task (bug fix, feature, refactor, TODO).
---

# Dev Skill — SStack Orchestrator Alias

`/dev` is an alias for `/sstack`, the lifecycle development orchestrator. It is
separate from `/spipe`, which is the focused BDD/spec-writing skill used inside
the pipeline.

## Usage

```
/dev <description of what to build or fix>
```

Argument: `$ARGUMENTS`

## Dispatch

Read `.claude/skills/sstack.md` and execute its orchestrator procedure with the user request. No differences — `/dev` and `/sstack` are the same pipeline.

## When to Use

| Scenario | Use |
|----------|-----|
| Any dev task (bug fix, feature, refactor, TODO) | `/dev` or `/sstack` |
| BDD/spec authoring only | `/spipe` |
| Large feature needing 15-phase doc artifacts | `/impl` |
| Research only, no implementation | `/research` |
| Design only, implementation later | `/design` |
| Post-implementation verification audit | `/verify` |
