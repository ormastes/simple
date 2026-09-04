# Frozen bootstrap worktree — DO NOT edit, commit, rebase, or fetch here

A bootstrap refuses admission if the source tree changes while it runs:

    error: refused incomplete Stage 2 admission provenance

That check compares `source-inputs-before.txt` with `source-inputs-after.txt`
and is CORRECT — a binary whose inputs moved mid-build has no provenance.

It fired on 2026-08-24 because the coordinator ran `git rebase origin/main` in
the build worktree during a Stage-2 run, pulling in a sibling lane's commit.
Two files changed under the running build (`src/app/__init__.spl` and
`src/lib/gc_async_mut/package/main.spl`) and ~10 minutes of compile were
discarded at the admission step.

This worktree exists so that can't recur: it is pinned detached and nothing
else runs in it. Do your editing anywhere else.
