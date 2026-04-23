# llm process

## pipeline process

One lead agent owns the user conversation. It refines the request, identifies the target feature and layers, loads the relevant expert knowledge, and delegates bounded work to pipeline skill experts or subagents.

Default feature pipeline: `/research` -> `/design` -> `/impl` -> `/verify` -> `/release`.

For the next implementation step, use [pipeline_next_step_plan.md](pipeline_next_step_plan.md). The plan defines how to load feature expert knowledge, layer expert knowledge, and pipeline-stage skills before generating the next step plan doc.

## knowledge model

- Feature experts live at `feature_expert/<feature>/skill.md`.
- Layer experts live at `layer_expert/<layer>/skill.md`.
- Initial expert templates live in `template/`.
- Reusable project-neutral skill and command knowledge lives in `skill_command/`.

When a new feature or layer expert is needed, copy the matching template from `template/`, create the expert directory, and update the new `skill.md` with links to the relevant project docs and source paths. When product knowledge changes during research, design, implementation, verification, or release, update the affected feature and layer expert skills.

## generator tool

Planned tool:

```bash
bin/simple llm-process-gen check
bin/simple llm-process-gen generate
bin/simple llm-process-gen generate --force
```

The tool should generate skills, commands, and subagent docs for Claude, Codex, and Gemini CLI. Subagent docs should hide MCP details behind task-oriented instructions; tool metadata stays in `tools.sdn` with `id` and `type`.

`check` alerts the user when generated docs drift from templates or the manifest. When generated docs change, the LLM should notify the user that `skill_command/` should be regenerated. `generate --force` regenerates all managed outputs after the user accepts the overwrite.

## skills & commands

Claude skill copies live under `skill_command/skills/pipe/<stage>/` and are grouped by pipeline stage. Each primary stage has direct `skill.md` and `tools.sdn` files; support skills live in subfolders with their own `skill.md` and `tools.sdn`. Tool rows include `id` and `type` where type is `cli` or `mcp`.
Pipeline-only Claude command copies live under `skill_command/command/`.

Additional extracted skills:

- Codex: `skill_command/skills/codex/<skill>/skill.md`
- Gemini: `skill_command/skills/gemini/<skill>/skill.md`
- Claude helpers: `skill_command/skills/claude/lib/<skill>/skill.md`
- Feature experts: `feature_expert/<feature>/skill.md`
- Layer experts: `layer_expert/<layer>/skill.md`
- Templates: `template/feature_skill.md`, `template/layer_skill.md`

Every extracted skill folder includes `tools.sdn` with `tools |id, type, name, purpose|`; `type` is `cli` or `mcp`.


Stage support skill grouping:

- Research: `research/skill.md`, `research/research_codex/`
- Design: `design/skill.md`, `design/arch/`, `design/gemini_ui_design/`, `design/theme_sync/`, `design/ui/`
- Implementation: `impl/skill.md`, `impl/dev/`, `impl/refactor/`, `impl/sspec_loop/`, `impl/sstack/`, `impl/stitch/`, `impl/sync/`
- Verification: `verify/skill.md`, `verify/bug_review/`
- Release: `release/skill.md`, `release/mail/`, `release/repo_and_pull_req/`

| Skill | Command | Copied skill file | Copied command file | Source skill file | Source command file |
|-------|---------|-------------------|---------------------|-------------------|---------------------|
| research | `/research` | `skill_command/skills/pipe/research/skill.md` | `skill_command/command/research.md` | `.claude/skills/research.md` | `.claude/commands/research.md` |
| design | `/design` | `skill_command/skills/pipe/design/skill.md` | `skill_command/command/design.md` | `.claude/skills/design.md` | `.claude/commands/design.md` |
| impl | `/impl` | `skill_command/skills/pipe/impl/skill.md` | `skill_command/command/impl.md` | `.claude/skills/impl.md` | `.claude/commands/impl.md` |
| verify | `/verify` | `skill_command/skills/pipe/verify/skill.md` | `skill_command/command/verify.md` | `.claude/skills/verify.md` | `.claude/commands/verify.md` |
| release | `/release` | `skill_command/skills/pipe/release/skill.md` | `skill_command/command/release.md` | `.claude/skills/release.md` | `.claude/commands/release.md` |
