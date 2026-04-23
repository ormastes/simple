# llm process

## skills & commands

Codex skills live under `.codex/skills/<name>/SKILL.md`. Matching command
entries live under `.codex/commands/<name>.md` and are invoked as `$<name>`.

Default feature pipeline: `$research` -> `$design` -> `$impl` -> `$verify` -> `$release`.

| Skill | Command | Skill file | Command file |
|-------|---------|------------|--------------|
| architecture | `$architecture` | `.codex/skills/architecture/SKILL.md` | `.codex/commands/architecture.md` |
| coding | `$coding` | `.codex/skills/coding/SKILL.md` | `.codex/commands/coding.md` |
| design | `$design` | `.codex/skills/design/SKILL.md` | `.codex/commands/design.md` |
| impl | `$impl` | `.codex/skills/impl/SKILL.md` | `.codex/commands/impl.md` |
| mdsoc-architecture-writing | `$mdsoc-architecture-writing` | `.codex/skills/mdsoc-architecture-writing/SKILL.md` | `.codex/commands/mdsoc-architecture-writing.md` |
| refactor | `$refactor` | `.codex/skills/refactor/SKILL.md` | `.codex/commands/refactor.md` |
| release | `$release` | `.codex/skills/release/SKILL.md` | `.codex/commands/release.md` |
| research | `$research` | `.codex/skills/research/SKILL.md` | `.codex/commands/research.md` |
| simple-ui | `$simple-ui` | `.codex/skills/simple-ui/SKILL.md` | `.codex/commands/simple-ui.md` |
| sync | `$sync` | `.codex/skills/sync/SKILL.md` | `.codex/commands/sync.md` |
| system_test | `$system_test` | `.codex/skills/system_test/SKILL.md` | `.codex/commands/system_test.md` |
| t32q | `$t32q` | `.codex/skills/t32q/SKILL.md` | `.codex/commands/t32q.md` |
| verify | `$verify` | `.codex/skills/verify/SKILL.md` | `.codex/commands/verify.md` |
