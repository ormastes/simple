# llm process

## skills & commands

Claude skill copies live under `skill_command/skills/`. Pipeline skills live under `skill_command/skills/pipe/`; non-pipeline skills live directly under `skill_command/skills/`.
Pipeline-only Claude command copies live under `skill_command/command/`.

Default feature pipeline: `/research` -> `/design` -> `/impl` -> `/verify` -> `/release`.

| Skill | Command | Copied skill file | Copied command file | Source skill file | Source command file |
|-------|---------|-------------------|---------------------|-------------------|---------------------|
| research | `/research` | `skill_command/skills/pipe/research.md` | `skill_command/command/research.md` | `.claude/skills/research.md` | `.claude/commands/research.md` |
| design | `/design` | `skill_command/skills/pipe/design.md` | `skill_command/command/design.md` | `.claude/skills/design.md` | `.claude/commands/design.md` |
| impl | `/impl` | `skill_command/skills/pipe/impl.md` | `skill_command/command/impl.md` | `.claude/skills/impl.md` | `.claude/commands/impl.md` |
| verify | `/verify` | `skill_command/skills/pipe/verify.md` | `skill_command/command/verify.md` | `.claude/skills/verify.md` | `.claude/commands/verify.md` |
| release | `/release` | `skill_command/skills/pipe/release.md` | `skill_command/command/release.md` | `.claude/skills/release.md` | `.claude/commands/release.md` |
