# Worktree Skill — JJ Workspace Isolation

**Purpose**: Isolated parallel development using JJ workspaces.

> **DO NOT use `EnterWorktree` / `ExitWorktree`** — those are git worktree tools.
> This project uses **jj workspaces** exclusively.

---

## Lifecycle

### 1. Create Workspace

```bash
jj workspace add ../simple-ws-<name> --name ws-<name>
```

Convention: `ws-<name>` where `<name>` describes the task (e.g., `ws-cuda-fix`, `ws-test-refactor`).

### 2. Work in Workspace

```bash
# Option A: cd into it
cd ../simple-ws-<name>
# ... make changes ...

# Option B: use absolute paths from main
bin/simple test ../simple-ws-<name>/test/some_spec.spl
```

### 3. Commit in Workspace

```bash
cd ../simple-ws-<name>
jj commit -m "feat: <description>"
```

### 4. Integrate Back to Main

From the **main** working copy:

```bash
cd /home/ormastes/dev/pub/simple  # main repo

# Get the change ID from the workspace commit
jj log  # find the workspace's change_id

# Squash workspace change into current main
jj squash --from <change_id>
```

### 5. Cleanup

```bash
jj workspace forget ws-<name>
rm -rf ../simple-ws-<name>
```

---

## Quick Reference

| Task | Command |
|------|---------|
| Create workspace | `jj workspace add ../simple-ws-<name> --name ws-<name>` |
| List workspaces | `jj workspace list` |
| Update stale workspace | `jj workspace update-stale` |
| Forget workspace | `jj workspace forget ws-<name>` |
| Delete workspace files | `rm -rf ../simple-ws-<name>` |

---

## Use Cases

### Parallel Development

Work on two features simultaneously without switching context:

```bash
# Create workspace for feature B while working on feature A
jj workspace add ../simple-ws-feature-b --name ws-feature-b

# Work on feature A in main, feature B in workspace
# Both see the same repo history
```

### Test While Editing

Run full test suite in workspace while editing in main:

```bash
jj workspace add ../simple-ws-test --name ws-test
cd ../simple-ws-test
bin/simple test  # runs without blocking main edits
```

### Experiments

Try an approach without affecting main working copy:

```bash
jj workspace add ../simple-ws-experiment --name ws-experiment
cd ../simple-ws-experiment
# ... try things ...

# If it worked: squash from main
# If it failed: just forget and delete
jj workspace forget ws-experiment
rm -rf ../simple-ws-experiment
```

---

## Agent Pattern

For task agents that need isolation:

```
1. Main agent creates workspace:
   jj workspace add ../simple-ws-<task> --name ws-<task>

2. Task agent works in workspace:
   - All file paths use ../simple-ws-<task>/... prefix
   - Commits with jj commit -m "..."

3. Main agent integrates:
   jj squash --from <change_id>

4. Main agent cleans up:
   jj workspace forget ws-<task>
   rm -rf ../simple-ws-<task>
```

### Agent Rules

- Task agents **MUST NOT** use `EnterWorktree` / `ExitWorktree`
- Task agents work via absolute paths or `cd` into workspace
- Only the **main agent** creates and destroys workspaces
- Always `jj workspace update-stale` if workspace was idle while main changed

---

## Workspace vs Git Worktree

| Feature | JJ Workspace | Git Worktree |
|---------|-------------|--------------|
| VCS integration | Native jj | Native git |
| Branch required | No | Yes |
| History sharing | Full (same repo) | Full (same repo) |
| Conflict handling | jj resolve | git merge |
| Cleanup | `forget` + `rm -rf` | `git worktree remove` |
| **Use in this project** | **YES** | **NO** |

---

## Troubleshooting

### Stale Workspace

If a workspace shows outdated content after main changed:

```bash
cd ../simple-ws-<name>
jj workspace update-stale
```

### Workspace Conflicts

If squashing a workspace change creates conflicts:

```bash
# Check which files conflict
jj st

# Resolve (same rules as /git-jj-sync)
# .sdn files: jj resolve --tool=internal:ours <file>
# .spl files: manual resolution
```

### Orphaned Workspaces

List and clean up forgotten workspaces:

```bash
jj workspace list
# For each unused workspace:
jj workspace forget <name>
rm -rf ../simple-ws-<name>
```

---

**Use this skill**: `/worktree` or `cat .claude/skills/worktree.md`
