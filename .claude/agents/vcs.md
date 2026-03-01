# VCS Agent - Version Control (JJ / Git)

**Use when:** Committing, pushing, viewing history, managing changes.
**Skills:** `/versioning`

## Quick Reference

| Task | JJ Command | Git Equivalent |
|------|-----------|----------------|
| Check status | `jj st` | `git status` |
| View changes | `jj diff` | `git diff` |
| Commit (snapshot) | `jj commit -m "message"` | `git add -A && git commit -m "message"` |
| Describe working copy | `jj describe -m "message"` | `git commit --amend -m "message"` (before push) |
| View history | `jj log` | `git log --oneline -20` |
| Push to remote | `jj bookmark set main -r @- && jj git push --bookmark main` | `git push origin main` |
| Fetch from remote | `jj git fetch` | `git fetch` |
| Rebase on latest | `jj rebase -d main@origin` | `git rebase origin/main` |
| Show change | `jj show <change_id>` | `git show <commit>` |
| Abandon change | `jj abandon <change_id>` | `git reset` |
| Squash into parent | `jj squash` | `git rebase -i` (squash) |
| Edit past change | `jj edit <change_id>` | `git rebase -i` (edit) |

## Key Concepts

- **Working copy IS a commit** - jj automatically tracks all file changes, no staging needed
- **No staging area** - every save is already tracked; `jj commit` snapshots current state
- **`describe` vs `commit`** - `describe` updates the current change's message; `commit` finalizes it and starts a new empty change
- **Change IDs are stable** - unlike git commit hashes, jj change IDs survive rebases
- **JJ-Change-Id trailer** - automatically appended to commit messages via config

## Standard Workflow

```bash
# 1. Make code changes (auto-tracked by jj)

# 2. Check what changed
jj st
jj diff

# 3. Commit
jj commit -m "feat: add new feature"

# 4. Push
jj bookmark set main -r @-
jj git push --bookmark main
```

## Fixing Past Changes

```bash
# Edit a past change (working copy moves to it)
jj edit <change_id>
# Make fixes, then create new change on top
jj new

# Squash current change into parent
jj squash

# Squash specific change into its parent
jj squash -r <change_id>

# Split a change
jj split -r <change_id>
```

## Workspace (Parallel Working Copies)

```bash
# Create workspace for parallel work
jj workspace add ../simple-ws2 --name ws2

# List workspaces
jj workspace list

# Remove workspace
jj workspace forget ws2

# Update stale workspace
jj workspace update-stale
```

## Rules

- NO branches - work directly on main
- LINEAR history - squash if needed
- Use jj as primary VCS (git commands available for tags, gh CLI)

## Commit Message Format

```
<type>: <short description>

[optional body]

JJ-Change-Id: <auto-appended>
```

Types: `feat`, `fix`, `refactor`, `docs`, `test`, `chore`, `perf`

## See Also

- `/versioning` - Full JJ + git workflow guide
