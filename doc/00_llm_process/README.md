# llm process

## skills & commands

Claude skill copies live under `skill_command/skills/pipe/<stage>/` and are grouped by pipeline stage. Each primary stage has direct `skill.md` and `tools.sdn` files; support skills live in subfolders with their own `skill.md` and `tools.sdn`. Tool rows include `id` and `type` where type is `cli` or `mcp`.
Pipeline-only Claude command copies live under `skill_command/command/`.

Additional extracted skills:

- Codex: `skill_command/skills/codex/<skill>/skill.md`
- Gemini: `skill_command/skills/gemini/<skill>/skill.md`
- Claude helpers: `skill_command/skills/claude/lib/<skill>/skill.md`

Every extracted skill folder includes `tools.sdn` with `tools |id, type, name, purpose|`; `type` is `cli` or `mcp`.


Stage support skill grouping:

- Research: `research/skill.md`, `research/research_codex/`
- Design: `design/skill.md`, `design/arch/`, `design/gemini_ui_design/`, `design/theme_sync/`, `design/ui/`
- Implementation: `impl/skill.md`, `impl/dev/`, `impl/refactor/`, `impl/sspec_loop/`, `impl/sstack/`, `impl/stitch/`, `impl/sync/`
- Verification: `verify/skill.md`, `verify/bug_review/`
- Release: `release/skill.md`, `release/mail/`, `release/repo_and_pull_req/`

Default feature pipeline: `/research` -> `/design` -> `/impl` -> `/verify` -> `/release`.

| Skill | Command | Copied skill file | Copied command file | Source skill file | Source command file |
|-------|---------|-------------------|---------------------|-------------------|---------------------|
| research | `/research` | `skill_command/skills/pipe/research/skill.md` | `skill_command/command/research.md` | `.claude/skills/research.md` | `.claude/commands/research.md` |
| design | `/design` | `skill_command/skills/pipe/design/skill.md` | `skill_command/command/design.md` | `.claude/skills/design.md` | `.claude/commands/design.md` |
| impl | `/impl` | `skill_command/skills/pipe/impl/skill.md` | `skill_command/command/impl.md` | `.claude/skills/impl.md` | `.claude/commands/impl.md` |
| verify | `/verify` | `skill_command/skills/pipe/verify/skill.md` | `skill_command/command/verify.md` | `.claude/skills/verify.md` | `.claude/commands/verify.md` |
| release | `/release` | `skill_command/skills/pipe/release/skill.md` | `skill_command/command/release.md` | `.claude/skills/release.md` | `.claude/commands/release.md` |
