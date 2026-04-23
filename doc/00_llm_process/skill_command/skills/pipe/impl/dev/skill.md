<!-- llm-process-gen: managed source=pipe_impl_dev_skill source_sha256=d0df8163a380c2334795d21db3ed31bd11047a2748862fcae048c9696a7e3ec2 content_sha256=d0df8163a380c2334795d21db3ed31bd11047a2748862fcae048c9696a7e3ec2 -->
---
name: dev
description: Alias for /sstack — same 8-phase BDD/TDD pipeline. Use for any dev task (bug fix, feature, refactor, TODO).
---

# Dev Skill — SStack Alias

`/dev` is an alias for `/sstack`. Same 8 phases, same state file, same quality gates, same cooperative workflow.

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
| Large feature needing 15-phase doc artifacts | `/impl` |
| Research only, no implementation | `/research` |
| Design only, implementation later | `/design` |
| Post-implementation verification audit | `/verify` |
