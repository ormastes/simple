# JJ (Jujutsu) as Primary VCS - Migration Research

**Date:** 2026-03-01
**Status:** Implemented

---

## Background

The Simple Language project has been using git as its sole VCS. Jujutsu (jj) 0.32.0 was installed and colocated with git (`.jj/` directory exists alongside `.git/`), and an MCP server (`bin/simple_jj_server`) was available, but all documentation and agent/skill files still referenced git-only commands.

### Why JJ?

- **No staging area** - every file change is automatically tracked; `jj commit` snapshots current state
- **Working copy is a commit** - eliminates the need for `git stash`, `git add`, or worrying about unstaged changes
- **Stable change IDs** - unlike git commit hashes, jj change IDs survive rebases and rewrites
- **First-class rewriting** - `jj edit`, `jj squash`, `jj split` replace complex `git rebase -i` workflows
- **Workspaces** - multiple working copies of the same repo at different changes
- **Conflict-aware** - conflicts are recorded in the commit graph, not blocking operations
- **Git-compatible** - colocated mode means git and jj share the same history; all git tools still work

---

## Migration Summary

### What Changed

| File | Change |
|------|--------|
| `~/.config/jj/config.toml` | Added `draft_commit_description` template for JJ-Change-Id trailer |
| `CLAUDE.md` | Updated agents table, skills table, and version control section |
| `.claude/agents/vcs.md` | Full rewrite: jj-primary with git equivalents |
| `.claude/skills/versioning.md` | Full rewrite: jj-primary workflow |
| `.claude/skills/release.md` | Replaced git commit/push commands with jj equivalents |
| `.claude/skills/rule.md` | Updated version control section |
| `.claude/agents/build.md` | Updated release process commands |

### What Stays as Git

- **Tags**: `git tag -a vX.Y.Z -m "message"` (jj doesn't create tags)
- **Tag push**: `git push origin vX.Y.Z`
- **GitHub CLI**: `gh pr`, `gh release`, `gh issue` (works with colocated git)
- **Rollback tag deletion**: `git tag -d` and `git push origin :refs/tags/`

---

## JJ-Change-Id Trailer

### Configuration

Added to `~/.config/jj/config.toml`:

```toml
[templates]
draft_commit_description = '''
concat(
  description,
  if(!description.contains("JJ-Change-Id:"),
    concat(
      if(!description.ends_with("\n"), "\n"),
      "\nJJ-Change-Id: " ++ change_id ++ "\n",
    ),
  ),
)
'''
```

### Purpose

Every commit message automatically includes a `JJ-Change-Id: <change_id>` trailer. This:
- Links git commits to their jj change IDs
- Enables traceability when viewing history with `git log`
- Deduplicates (won't add if already present)

---

## Workspace Usage Guide

JJ workspaces provide parallel working copies of the same repository, each checked out to a different change.

### Creating a Workspace

```bash
jj workspace add ../simple-ws2 --name ws2
```

This creates a new directory with its own working copy. Both workspaces share the same repository state.

### Use Cases

1. **Parallel development** - work on two unrelated changes simultaneously
2. **Testing** - run tests in one workspace while editing in another
3. **Comparison** - compare behavior between two different changes

### Management

```bash
jj workspace list           # List all workspaces
jj workspace forget ws2     # Remove a workspace
jj workspace update-stale   # Refresh after changes in another workspace
```

---

## Command Mapping

| Operation | JJ | Git |
|-----------|-----|------|
| Status | `jj st` | `git status` |
| Diff | `jj diff` | `git diff` |
| Commit | `jj commit -m "msg"` | `git add -A && git commit -m "msg"` |
| Amend message | `jj describe -m "msg"` | `git commit --amend -m "msg"` |
| History | `jj log` | `git log --oneline` |
| Show | `jj show <id>` | `git show <hash>` |
| Push | `jj bookmark set main -r @- && jj git push --bookmark main` | `git push origin main` |
| Fetch | `jj git fetch` | `git fetch` |
| Rebase | `jj rebase -d main@origin` | `git rebase origin/main` |
| Undo | `jj abandon <id>` | `git reset` |
| Squash | `jj squash` | (interactive rebase) |
| Edit past | `jj edit <id>` | (interactive rebase) |
| Stash | Not needed (WC is commit) | `git stash` |

---

## Workflow Differences

### No Staging

Git requires explicit `git add` before committing. JJ tracks all file changes automatically. `jj commit` snapshots everything in the working directory.

### Working Copy as Commit

In git, uncommitted changes float above the commit graph. In jj, the working copy IS a commit (the `@` revision). Every file save updates this commit. `jj commit` finalizes it and creates a new empty working copy commit.

### Describe vs Commit

- `jj describe -m "msg"` - sets the message on the current working copy commit without finalizing
- `jj commit -m "msg"` - finalizes the current change and starts a new empty one

### Bookmarks (not Branches)

JJ uses "bookmarks" instead of "branches". A bookmark is a named pointer to a change, similar to a git branch but more explicit. The main workflow uses `jj bookmark set main -r @-` to point the `main` bookmark at the just-committed change.

---

## MCP Server

The project includes a JJ MCP server at `bin/simple_jj_server` providing:
- 48 tools for jj operations (commit, diff, log, rebase, etc.)
- 27 tools for additional functionality

This enables AI agents to interact with jj programmatically.

---

## Remaining Git Dependencies

| Feature | Why Git | JJ Alternative |
|---------|---------|----------------|
| Tags | `jj` doesn't support tag creation | None - use `git tag` |
| GitHub CLI | `gh` reads `.git/` | Works with colocated repo |
| CI/CD | GitHub Actions uses git | Colocated mode is transparent |
| Submodules | Not supported by jj | None currently |
