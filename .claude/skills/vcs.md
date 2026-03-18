---
name: vcs
description: JJ (Jujutsu) version control workflow, git sync, conflict resolution, and atomic push
---

# VCS Skill — JJ (Jujutsu) + Git Workflow & Sync

**Purpose**: Complete version control reference — JJ basics, git equivalents, atomic sync workflow, conflict resolution, and error handling.

---

## 1. Quick Reference

### Important Rules

1. **NO BRANCHES** - Work directly on `main`, do not create feature branches
2. **Use jj** as primary VCS (git available for tags and `gh` CLI)
3. **LINEAR HISTORY** - Rebase, never merge. Squash if needed before push
4. **NEVER force push** — if push fails, re-fetch and rebase

### JJ Command Reference

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

### Standard Workflow

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

### Workspace (Parallel Working Copies)

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

### Commit Message Format

```
<type>: <short description>

[optional body]

JJ-Change-Id: <auto-appended by config>
```

Types: `feat`, `fix`, `refactor`, `docs`, `test`, `chore`, `perf`, `build`

---

## 2. Git Equivalents

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

### Remaining Git Dependencies

These operations still use git directly:
- **Tags**: `git tag -a vX.Y.Z -m "message"` and `git push origin vX.Y.Z`
- **GitHub CLI**: `gh pr`, `gh release`, `gh issue` (works with colocated git)

---

## 3. Atomic Commit-Fetch-Rebase-Push Workflow

Run these commands sequentially — each step depends on the previous:

```bash
# 1. Commit local changes
jj commit -m "<type>: <message>"

# 2. Fetch remote
jj git fetch

# 3. Rebase on latest remote main
jj rebase -d main@origin

# 4. Set bookmark for push
jj bookmark set main -r @-

# 5. Push
jj git push --bookmark main
```

### One-Liner (for scripts)

```bash
jj commit -m "<msg>" && jj git fetch && jj rebase -d main@origin && jj bookmark set main -r @- && jj git push --bookmark main
```

### Pre-Sync Checklist

Before running the sync workflow:

- [ ] All tests pass: `bin/simple test`
- [ ] No lint warnings: `bin/simple build lint`
- [ ] No uncommitted experiments you want to discard
- [ ] Commit message follows convention: `<type>: <description>`

### Undo and Recovery

```bash
# Undo the last jj operation (any of: commit, rebase, squash, etc.)
jj undo

# View operation history
jj op log

# Restore to a specific operation
jj op restore <operation_id>
```

**Safe recovery flow:**
1. `jj op log` — find the operation before things went wrong
2. `jj op restore <op_id>` — restore to that state
3. Retry the sync workflow

---

## 4. SDN Conflict Resolution

### SDN Files (`.sdn`)

SDN config/data files: **always pick ours** (local version wins).

```bash
jj resolve --tool=internal:ours <file.sdn>
```

### Simple Source Files (`.spl`, `.shs`)

Source files require **manual resolution**:

```bash
# 1. See which files have conflicts
jj st

# 2. Open conflicted file — look for conflict markers
#    <<<<<<< ... ||||||| ... ======= ... >>>>>>>

# 3. Edit to resolve, then mark resolved
jj resolve <file.spl>
```

### Bulk SDN Resolution

If multiple SDN files conflict:

```bash
# Resolve all .sdn files with "ours"
for f in $(jj st | grep '\.sdn' | awk '{print $2}'); do
    jj resolve --tool=internal:ours "$f"
done
```

### Post-Rebase SDN Regeneration

After resolving SDN conflicts (or after any merge that touched `.sdn` files),
regenerate databases to incorporate changes from the other branch:

```bash
bin/simple test              # Regenerates FeatureDB, TestDB, feature.md, test_result.md
bin/simple bug-gen           # Regenerates BugDB, bug_report.md
bin/simple todo-scan         # Regenerates TODO.md
```

**Git note:** `.gitattributes` sets `*.sdn merge=ours` — git silently keeps the
current branch version on conflict (requires `git config merge.ours.driver true`).
jj does NOT support this (issues #5264, #8071), so jj conflicts require manual
`jj resolve` followed by regeneration. See `doc/db_lists.md` for the full registry.

---

## 5. Error Handling

### Fetch Failures

| Error | Cause | Fix |
|-------|-------|-----|
| `Could not resolve host` | No network | Check connection, retry |
| `Authentication failed` | SSH/token expired | `ssh-add` or refresh token |
| `Repository not found` | Wrong remote URL | `jj git remote list`, fix URL |

### Rebase Failures

| Error | Cause | Fix |
|-------|-------|-----|
| `Conflict in ...` | Divergent changes | See Conflict Resolution above |
| `No main@origin` | Remote not fetched | Run `jj git fetch` first |
| `Immutable revision` | Trying to rebase published | `jj new` to create fresh change |

### Push Failures

| Error | Cause | Fix |
|-------|-------|-----|
| `Bookmark moved unexpectedly` | Someone pushed between fetch and push | Re-fetch and rebase: `jj git fetch && jj rebase -d main@origin` |
| `Non-fast-forward` | History diverged | Re-fetch, rebase, try again |
| `Permission denied` | No write access | Check repo permissions |

---

## Integration with `/impl`

Phase 15 of the `/impl` workflow invokes this skill. The impl workflow ensures all tests pass and duplication checks are clean before calling sync.

---

**Use this skill**: `/vcs` or `cat .claude/skills/vcs.md`
