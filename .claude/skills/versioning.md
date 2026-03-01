# Versioning Skill - JJ (Jujutsu) + Git Workflow

## Important Rules

1. **NO BRANCHES** - Work directly on `main`, do not create feature branches
2. **Use jj** as primary VCS (git available for tags and `gh` CLI)
3. **LINEAR HISTORY** - Keep history linear, squash if needed before push

## JJ Command Reference

| Task | JJ Command |
|------|-----------|
| Check status | `jj st` |
| View changes | `jj diff` |
| Commit | `jj commit -m "message"` |
| Describe current | `jj describe -m "message"` |
| View history | `jj log` |
| Show change | `jj show <change_id>` |
| Push | `jj bookmark set main -r @- && jj git push --bookmark main` |
| Fetch | `jj git fetch` |
| Rebase on latest | `jj rebase -d main@origin` |
| Abandon change | `jj abandon <change_id>` |
| Squash into parent | `jj squash` |
| Edit past change | `jj edit <change_id>` |
| New empty change | `jj new` |
| Split change | `jj split -r <change_id>` |
| Move changes | `jj move --from <src> --to <dst>` |

## Standard Workflow

### Making Changes (Work on Main)
```bash
# 1. Make your code changes (auto-tracked, no staging needed)

# 2. Check what changed
jj st
jj diff

# 3. Commit
jj commit -m "feat: add new feature"

# 4. Push
jj bookmark set main -r @-
jj git push --bookmark main
```

### Fetch and Rebase
```bash
# Get latest from remote
jj git fetch

# Rebase your work on top of latest main
jj rebase -d main@origin
```

### Fixing Past Changes
```bash
# Edit a past change directly
jj edit <change_id>
# Make your fixes (auto-tracked)
# Return to latest
jj new

# Squash current change into its parent
jj squash

# Squash with custom message
jj squash -m "combined message"

# Amend current change description
jj describe -m "updated message"
```

## Workspace (Parallel Working Copies)

JJ workspaces allow multiple working copies of the same repo, each at a different change.

```bash
# Create a new workspace
jj workspace add ../simple-ws2 --name ws2

# List all workspaces
jj workspace list

# Forget (remove) a workspace
jj workspace forget ws2

# Update a stale workspace after changes in another
jj workspace update-stale
```

Use workspaces for:
- Working on two changes simultaneously
- Running tests on one change while editing another
- Comparing behavior between changes

## Commit Message Format

```
<type>: <short description>

[optional body]

JJ-Change-Id: <auto-appended by config>
```

Types: `feat`, `fix`, `refactor`, `docs`, `test`, `chore`, `perf`

## Git Equivalents Reference

For users familiar with git:

| Git | JJ |
|-----|-----|
| `git status` | `jj st` |
| `git diff` | `jj diff` |
| `git add -A && git commit -m "msg"` | `jj commit -m "msg"` |
| `git commit --amend` | `jj describe -m "msg"` or `jj squash` |
| `git log --oneline` | `jj log` |
| `git show <hash>` | `jj show <change_id>` |
| `git push origin main` | `jj bookmark set main -r @- && jj git push --bookmark main` |
| `git pull origin main` | `jj git fetch && jj rebase -d main@origin` |
| `git rebase -i` | `jj edit`, `jj squash`, `jj split` |
| `git stash` | Not needed (working copy is a commit) |
| `git tag -a v1.0` | `git tag -a v1.0` (use git for tags) |

## Remaining Git Dependencies

These operations still use git directly:
- **Tags**: `git tag -a vX.Y.Z -m "message"` and `git push origin vX.Y.Z`
- **GitHub CLI**: `gh pr`, `gh release`, `gh issue` (works with colocated git)
