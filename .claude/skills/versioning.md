# Versioning Skill - Jujutsu (jj) Workflow

**CRITICAL: This project uses Jujutsu (jj), NOT Git!**

## Important Rules

1. **NO BRANCHES** - Work directly on `main`, do not create feature branches
2. **NO GIT** - Never use git commands, only jj
3. **LINEAR HISTORY** - Keep history linear, squash if needed before push

## Quick Reference

| Task | Command |
|------|---------|
| Check status | `jj status` |
| View changes | `jj diff` |
| Describe change | `jj describe -m "message"` |
| View history | `jj log` |
| Push to remote | `jj git push --bookmark main` |
| Set main to current | `jj bookmark set main -r @` |
| Create new change | `jj new` |
| Abandon change | `jj abandon` |
| Squash changes | `jj squash` |
| Edit past change | `jj edit <change-id>` |
| Show change details | `jj show <change-id>` |

## DO NOT USE These Git Commands

- `git add`, `git commit`, `git push`, `git pull`
- `git checkout`, `git branch`, `git merge`
- `git stash`, `git rebase`

The `.git` directory exists only for remote sync - all local operations use `jj`.

## Standard Workflow

### Making Changes (Work on Main)
```bash
# 1. Make your code changes (files are auto-tracked)
# 2. Check what changed
jj status
jj diff

# 3. Describe the current change
jj describe -m "feat: Add new feature

Co-Authored-By: Claude Opus 4.5 <noreply@anthropic.com>"

# 4. Verify linear history
jj log

# 5. Set main bookmark and push
jj bookmark set main -r @
jj git push --bookmark main
```

### Creating a New Change
```bash
# Create new empty change on top of current
jj new

# Create new change with message
jj new -m "Start working on X"
```

### Fixing Past Changes
```bash
# Edit a past change
jj edit <change-id>

# Make fixes, then return to latest
jj new

# Or squash fix into parent
jj squash
```

### Handling Diverged History
```bash
# If branches diverge, abandon the diverged one
jj abandon <diverged-change-id>

# Ensure linear history before pushing
jj log
```

## Key Concepts

1. **Auto-snapshots**: jj automatically tracks all file changes
2. **Working copy**: Always on a "draft" change
3. **No staging area**: All changes are automatically included
4. **Immutable history**: Changes are immutable once pushed
5. **Change IDs**: Use short IDs from `jj log` (e.g., `abc123`)

## Commit Message Format

```
<type>: <short description>

[optional body]

[optional footer]
```

Types: `feat`, `fix`, `refactor`, `docs`, `test`, `chore`, `perf`

## See Also

- `doc/plans/27_jj_integration.md` - Full JJ integration details
- AGENTS.md - Agent-specific version control guidelines
