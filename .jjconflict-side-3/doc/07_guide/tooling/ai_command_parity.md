# AI Command Parity

This repository uses the same core workflow names across Claude, Codex, and Gemini:

- `research`
- `design`
- `impl`
- `verify`
- `release`
- `sync`
- `refactor`
- `coding`

## Native Invocation by Tool

### Claude Code

Claude uses slash commands backed by `.claude/skills/`:

- `/research`
- `/design`
- `/impl`
- `/verify`
- `/release`

### Gemini CLI

Gemini uses slash commands backed by `.gemini/commands/*.toml`:

- `/research`
- `/design`
- `/impl`
- `/verify`
- `/release`

### Codex CLI

Codex uses skills and project instructions, not the Gemini command registry format:

- `$research`
- `$design`
- `$impl`
- `$verify`
- `$release`

Codex reads:

- `AGENTS.md`
- `.codex/skills/*/SKILL.md`
- `.codex/config.toml`

## Parity Convention

To keep the repo easy to navigate, `scripts/setup.sh` creates `.codex/commands/<name>.md` symlinks pointing at `.codex/skills/<name>/SKILL.md`.

This gives Codex and Gemini the same visible command names in the tree, but it does **not** mean Codex has native Gemini-style slash command support.

Use this mapping:

| Canonical name | Gemini | Codex |
|----------------|--------|-------|
| research | `/research` | `$research` |
| design | `/design` | `$design` |
| impl | `/impl` | `$impl` |
| verify | `/verify` | `$verify` |
| release | `/release` | `$release` |
| sync | `/sync` | `$sync` |
| refactor | `/refactor` | `$refactor` |
| coding | `/coding` | `$coding` |

## Notes

- Gemini command definitions live in `.gemini/commands/*.toml`.
- Codex skill bodies live in `.codex/skills/*/SKILL.md`.
- If Codex later gains a native per-project command registry, `.codex/commands/` can be used as the migration anchor.
