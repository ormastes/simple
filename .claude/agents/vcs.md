# VCS Agent - Version Control (Jujutsu)

**Use when:** Committing, pushing, viewing history, managing changes.
**Skills:** `/versioning`

## CRITICAL: Use jj, NOT git!

This project uses Jujutsu (jj). NEVER use git commands.

## Quick Reference

| Task | Command |
|------|---------|
| Check status | `jj status` |
| View changes | `jj diff` |
| Describe change | `jj describe -m "message"` |
| View history | `jj log` |
| Push to remote | `jj bookmark set main -r @ && jj git push --bookmark main` |
| Create new change | `jj new` |
| Abandon change | `jj abandon` |
| Squash into parent | `jj squash` |
| Edit past change | `jj edit <change-id>` |

## Standard Workflow

```bash
# 1. Make code changes (auto-tracked)
# 2. Check what changed
jj status
jj diff

# 3. Describe the change
jj describe -m "feat: Add new feature

Co-Authored-By: Claude Opus 4.6 <noreply@anthropic.com>"

# 4. Push
jj bookmark set main -r @
jj git push --bookmark main
```

## Rules

- NO branches - work directly on main
- NO git commands - only jj
- LINEAR history - squash if needed
- Auto-snapshots: jj tracks all file changes automatically
- No staging area: all changes included automatically

## Commit Message Format

```
<type>: <short description>

[optional body]
```

Types: `feat`, `fix`, `refactor`, `docs`, `test`, `chore`, `perf`

## See Also

- `/versioning` - Full jj workflow guide
