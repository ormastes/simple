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

## It recurred on 2026-09-05, in the shared checkout

Three bootstrap attempts run directly in `/Users/ormastes/simple` all failed at
the same place:

    error: refused incomplete Stage 2 admission provenance   (exit 4)

Cause was the same as 2026-08-24 but the trigger was different: nobody rebased.
Concurrent sessions simply *edited* `src/app/llm_caret/**` while the build ran,
and the admission gate's before/after source snapshot differed by 14 entries.
The same work then completed Stage 2 on the first try in a private worktree
pinned to a commit. Full incident, including the input-by-input comparison:
`doc/08_tracking/bug/bootstrap_stage2_admission_refused_by_concurrent_source_edits_2026-09-05.md`.

The shared checkout is not a place a bootstrap can succeed. Do not retry there.

## How to run a bootstrap correctly

1. **Pin a private worktree to a commit.** Detached, so nothing can move it:

   ```bash
   git worktree add --detach <build-dir> <sha>
   ```

   Nothing else — no editor, no peer session, no sync job — touches
   `<build-dir>` until admission has completed.

2. **Give it a real `src/compiler_rust/target`.** Symlinking it at the main
   checkout's `target/` to avoid the multi-GB rebuild does **not** work: the run
   fails immediately with

       error: failed to fingerprint Rust seed inputs

   Pay the rebuild, or use a separate real directory. (See the bug record's closing note, lines 127-130.)

3. **Send the wrapper's output to a file, both streams.** A wrapper launched as
   `sh -c '… ; echo BOOTSTRAP_EXIT=$?'` puts the bootstrap's own stdout and
   stderr on a terminal and nowhere on disk — in the 2026-09-05 incident the
   *only* copy of the actual error text was lost that way, costing a full run.
   Redirect explicitly:

   ```bash
   sh scripts/bootstrap/<script> > <log> 2>&1; echo "exit=$?" >> <log>
   ```

4. **Decide "did this stage build?" from the artifact, not from a log read.**
   The other run lost to diagnosis was a tool reporting
   `the log was NEVER CREATED, so nothing ever executed` for a stage that had in
   fact built successfully — it was reading a stale or wrong path. Check the
   stage binary's existence and mtime before concluding anything about a log.

5. **Read the verdict, then stop.** Exit 4 with the provenance message means the
   tree moved under the build. It is not a compiler bug and re-running in the
   same location will reproduce it.

Which bootstrap script is the sanctioned one (`scripts/bootstrap/bootstrap-from-scratch.sh`), and how `bin/simple build bootstrap` differs from it, is in
`.claude/rules/bootstrap.md`.
