# Jujutsu Sync Guide

This guide records the repo-local sync policy for pushing `main` with `jj`.
It complements `.codex/skills/sync/SKILL.md`.

## Standard Flow

1. Check the working copy:

   ```bash
   jj status
   jj log --no-graph -r 'main | main@origin | git_head() | @- | @'
   ```

2. Record the tracked-file guard:

   ```bash
   FILE_COUNT_BEFORE=$(git ls-files | wc -l | tr -d ' ')
   ```

3. Commit the current working copy with a Lore-format message.

4. Fetch and rebase linearly:

   ```bash
   jj git fetch
   jj rebase -d main@origin
   ```

5. Recheck the file count before moving bookmarks:

   ```bash
   FILE_COUNT_AFTER=$(git ls-files | wc -l | tr -d ' ')
   test "$FILE_COUNT_AFTER" -ge "$FILE_COUNT_BEFORE"
   ```

6. Move and push `main`:

   ```bash
   jj bookmark set main -r @-
   jj git push --bookmark main
   ```

If HTTPS push fails because an environment `GITHUB_TOKEN` is invalid, retry with
that variable unset so Git can use the stored GitHub CLI credential:

```bash
env -u GITHUB_TOKEN jj git push --bookmark main
```

## Orphan And Stale Heads

Do not bulk cherry-pick every old `worktree-agent-*`, browser milestone, or
conflict head into `main`. Treat orphan heads as candidates only when all of the
following hold:

- The bookmark is not already represented by `main` (`jj diff --stat -r
  'main..<bookmark>'` is non-empty).
- The change has no unresolved conflicts.
- The scope is still relevant to the current sync request.
- The change can be validated or has clear existing evidence.

Skip stale candidates when they are days old, conflict-marked, empty relative to
`main`, or belong to a separate topic that needs review. Record the skip in the
commit message using a `Rejected:` trailer.

## Concurrent Workspace Writes

This repo may have other jj workspaces or tools importing Git changes while a
sync is running. If `jj status` changes after a commit, repeat the commit and
file-count checks until the working copy is clean, or stop before push and report
the moving workspace as the blocker.
