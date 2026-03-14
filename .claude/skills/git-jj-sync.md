# Git-JJ-Sync Skill — One-Step Commit-Fetch-Rebase-Push

**Purpose**: Synchronize local work with remote in a single atomic workflow using jj.

---

## Full Sync Workflow

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

---

## Error Handling

### Fetch Failures

| Error | Cause | Fix |
|-------|-------|-----|
| `Could not resolve host` | No network | Check connection, retry |
| `Authentication failed` | SSH/token expired | `ssh-add` or refresh token |
| `Repository not found` | Wrong remote URL | `jj git remote list`, fix URL |

### Rebase Failures

| Error | Cause | Fix |
|-------|-------|-----|
| `Conflict in ...` | Divergent changes | See Conflict Resolution below |
| `No main@origin` | Remote not fetched | Run `jj git fetch` first |
| `Immutable revision` | Trying to rebase published | `jj new` to create fresh change |

### Push Failures

| Error | Cause | Fix |
|-------|-------|-----|
| `Bookmark moved unexpectedly` | Someone pushed between fetch and push | Re-fetch and rebase: `jj git fetch && jj rebase -d main@origin` |
| `Non-fast-forward` | History diverged | Re-fetch, rebase, try again |
| `Permission denied` | No write access | Check repo permissions |

---

## Conflict Resolution

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

---

## Undo and Recovery

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

## Rules

1. **NEVER force push** — if push fails, re-fetch and rebase
2. **NEVER create branches** — work directly on `main`
3. **LINEAR HISTORY** — rebase, never merge
4. **SDN conflicts = ours** — always pick local for config/data
5. **Source conflicts = manual** — never auto-resolve `.spl` files
6. **Always fetch before rebase** — stale remote refs cause errors

---

## Pre-Sync Checklist

Before running the sync workflow:

- [ ] All tests pass: `bin/simple test`
- [ ] No lint warnings: `bin/simple build lint`
- [ ] No uncommitted experiments you want to discard
- [ ] Commit message follows convention: `<type>: <description>`

Types: `feat`, `fix`, `refactor`, `docs`, `test`, `chore`, `perf`, `build`

---

## Integration with `/impl`

Phase 15 of the `/impl` workflow invokes this skill. The impl workflow ensures all tests pass and duplication checks are clean before calling sync.

---

**Use this skill**: `/git-jj-sync` or `cat .claude/skills/git-jj-sync.md`
