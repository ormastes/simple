# Versioning Skill - Jujutsu (jj) Workflow

**CRITICAL: This project uses Jujutsu (jj), NOT Git!**

## Quick Reference

| Task | Command |
|------|---------|
| Check status | `jj status` |
| View changes | `jj diff` |
| Describe change | `jj describe -m "message"` |
| View history | `jj log` |
| Push to remote | `jj git push` |
| Create new change | `jj new` |
| Create bookmark | `jj bookmark create <name>` |
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

### Making Changes
```bash
# 1. Make your code changes (files are auto-tracked)
# 2. Check what changed
jj status
jj diff

# 3. Describe the current change
jj describe -m "feat: Add new feature"

# 4. Verify
jj log

# 5. Push when ready
jj git push
```

### Creating a New Change
```bash
# Create new empty change on top of current
jj new

# Create new change with message
jj new -m "Start working on X"
```

### Bookmarks (Branches)
```bash
# Create bookmark at current change
jj bookmark create feature-name

# Push bookmark to remote
jj git push --bookmark feature-name
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
