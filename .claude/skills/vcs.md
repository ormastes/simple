# VCS Skill - JJ (Jujutsu) + Git Workflow

## Rules
1. **NO BRANCHES** — work directly on `main`
2. **Use jj** as primary VCS (git for tags and `gh` CLI only)
3. **LINEAR HISTORY** — rebase, never merge

## Quick Reference

| Task | Command |
|------|---------|
| Status | `jj st` |
| Diff | `jj diff` |
| Commit | `jj commit -m "type: message"` |
| Describe | `jj describe -m "message"` |
| Log | `jj log` |
| Show | `jj show <change_id>` |
| Push | `jj bookmark set main -r @- && jj git push --bookmark main` |
| Fetch | `jj git fetch` |
| Rebase | `jj rebase -d main@origin` |
| Squash | `jj squash` |
| Edit past | `jj edit <change_id>` |
| Abandon | `jj abandon <change_id>` |
| Undo | `jj undo` |

## Atomic Sync Workflow

```bash
jj commit -m "<type>: <msg>"
jj git fetch
jj rebase -d main@origin
jj bookmark set main -r @-
jj git push --bookmark main
```

Pre-sync: tests pass (`bin/simple test`), no lint warnings (`bin/simple build lint`).

## Conflict Resolution

- SDN files: `jj resolve --tool=internal:ours <file.sdn>` (local wins)
- Source files: manual edit → `jj resolve <file.spl>`
- Post-resolve: `bin/simple test && bin/simple bug-gen && bin/simple todo-scan`

## Recovery

```bash
jj op log                    # View operation history
jj op restore <op_id>       # Restore to previous state
```

## Workspace (Parallel Copies)

```bash
jj workspace add ../simple-ws2 --name ws2
jj workspace list
jj workspace forget ws2
jj workspace update-stale
```

## Commit Types
`feat`, `fix`, `refactor`, `docs`, `test`, `chore`, `perf`, `build`

## Git Dependencies
Tags: `git tag -a vX.Y.Z -m "msg" && git push origin vX.Y.Z`
GitHub CLI: `gh pr`, `gh release`, `gh issue`
