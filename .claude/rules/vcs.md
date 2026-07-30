---
paths:
  - "**"
alwaysApply: false
---
# Version Control

- Use **jj** (Jujutsu) as primary VCS, colocated with git
- **NEVER create branches** - work directly on `main`
- Commit: `jj commit -m "message"` (auto-tracks all changes, no staging needed)
- Push: `sj bookmark set main -r @- && sj git push --bookmark main`
- Fetch: `sj raw jj git fetch && sj raw jj rebase -d main@origin`

## When `jj git push` fails ("External git program failed")

Origin's HTTPS token is dead. Push the rebased tip directly over SSH, then re-sync tracking:

```bash
TIP=$(jj --ignore-working-copy log -r '@-' --no-graph -T 'commit_id')
GIT_SSH_COMMAND="ssh -o BatchMode=yes -i ~/.ssh/id_ed25519_this_mac" \
  git push git@github.com:ormastes/simple.git "$TIP":refs/heads/main
GIT_SSH_COMMAND="ssh -o BatchMode=yes -i ~/.ssh/id_ed25519_this_mac" jj --ignore-working-copy git fetch
```

Always verify with `git ls-remote` after — a clean-looking exit is not proof the content landed.

## Rebase conflict loop (root-first)

Parallel agent sessions force-push main continuously; a rebase can conflict a whole chain. Never resolve at the tip — resolve the ROOT and let descendants auto-rebase, looping until empty:

```bash
jj --ignore-working-copy log -r 'roots((main@origin..@) & conflicts())'   # find root
jj --ignore-working-copy restore --from <chosen-side> --to <ROOT> <paths...>
```

Side policy is per-path: paths whose latest truth is local restore from the pre-rebase local tip sha; paths already superseded upstream restore from `main@origin` (verify by symbol-grep on origin first). `--ignore-working-copy` is required — it skips the WC snapshot and dodges "Concurrent checkout" races.

## Pre-push guards

- **No `.jjconflict-*` trees in the outgoing range — run `sh scripts/check/check-no-conflict-tree-push.shs` (exit 0 = safe).** With no argument it checks `main@origin..@-`, exactly what `jj git push --bookmark main` sends. **`jj git push` does NOT block a conflict commit**; on 2026-07-25 one was pushed and `main` carried no source files at all across two commits until it was repaired. A jj conflict commit's git tree contains *only* `.jjconflict-base-0/` and `.jjconflict-side-N/`, so a clone gets an empty repo. Symptom to recognise: `git cat-file -p <sha>:<path>` says *"exists on disk, but not in <sha>"* — that reads like one missing file but means the whole tree is gone; confirm with `git ls-tree --name-only <sha>`. Range only — never `main@{0}` (that sweeps the whole reflog).
- **No literal conflict-marker text in pushed file content — run `sh scripts/check/check-no-conflict-markers-push.shs` (exit 0 = safe).** Same default range as the tree guard. This catches a different failure than the one above: a `jj rebase` can inject conflict-marker text into file CONTENT (both jj's `<<<<<<< conflict N of M` / `%%%%%%%` / `>>>>>>> ... ends` style and git's classic `<<<<<<< HEAD` / `=======` / `>>>>>>>` style) without the commit being tree-conflicted, so the tree guard misses it. On 2026-07-30 exactly this happened: a rebase wrote markers into 38 tracked files, including the Rust seed `src/compiler_rust/runtime/src/value/mod.rs`, breaking every seed build. The guard flags a file only when it has a matching open+close marker pair, so prose that merely mentions marker syntax (e.g. this file, jj's own vendored docs) doesn't false-positive.
- No leaked markers in previously-conflicted files: `git grep -c '^<<<<<<<' $TIP -- <paths>` must be 0.
- Stale `.git/index.lock` with no live holder: `find .git/index.lock -mmin +5 -delete`. Check `pgrep -af 'jj (rebase|restore)'` first — a D-state jj may still be progressing (verify via `/proc/PID/io` deltas) and must not be killed.
- Edit-tool changes are not auto-snapshotted: commit immediately after editing, and re-verify file content (`grep`) after any `workspace update-stale` — a parallel-session reconcile can silently clobber uncommitted edits.

## Sync must never clobber (anti-revert protocol)

Hourly/periodic "sync" commits (e.g. `chore(sync): session work products`) have
repeatedly REVERTED other sessions' landed fixes by snapshotting a **stale**
whole working copy and pushing it — while falsely claiming "fixes preserved at
origin versions". A sync that reverts is worse than no sync. Mandatory:

1. **Rebase before you snapshot.** `sj raw jj git fetch && sj raw jj rebase -d
   main@origin` FIRST, resolve, and only then snapshot the WC. Never commit a WC
   captured before the latest fetch.
2. **Never whole-WC-commit files this session didn't change.** A sync commit
   carries only files THIS session actually authored. Do not `jj commit -a` /
   `git add -A` a full stale tree. Scope the commit to your changed paths.
3. **Revert guard (blocks the push).** For every file in the outgoing range,
   confirm the change is a forward delta, not a rewind of someone else's fix:
   `git diff main@origin..$TIP -- <path>` must not restore an older version of a
   file you didn't touch. If any hunk reintroduces code origin already moved past
   (symbol-grep origin to confirm), STOP and drop that path — do not push.
4. **Never write "fixes preserved at origin versions"** unless you verified it by
   symbol-grep on `main@origin` for each fix. An unverified preservation claim is
   how the last three clobbers hid themselves.

Non-code artifacts (docs, skills, workflows, spipe state) may sync freely; the
danger is only `src/**`, `scripts/**`, and other product code — hold those to the
guards above. Upgrade path: a `scripts/check/` pre-push hook that fails when the
outgoing range reverts a product file the committer didn't author. (The
conflict-tree half of this is now implemented as
`scripts/check/check-no-conflict-tree-push.shs`; the revert-detection half is
still manual.)

**Rebasing onto a parallel session's resolution: diff both directions.** When
two sessions fix the same file, the newer origin version is not automatically a
superset. On 2026-07-25 origin's resolution of `make_os_disk.c` kept most of the
local fixes but replaced fixed-cluster geometry with dynamic sizing — so the
local copy was *behind* on one axis and *ahead* on three. Overwriting either way
would have reverted real work. Check `diff -u origin_version local_version` and
read **both** the `-` and `+` sides before choosing; often the answer is that
origin already supersedes you and the right move is to drop your commit.

## LLM wiki before commit

Before committing feature work, refresh the related LLM wiki entries so the
commit ships with current knowledge links: the affected
`doc/00_llm_process/feature_expert/<feature>/skill.md` and
`doc/00_llm_process/layer_expert/<layer>/skill.md`. Templates:
`.spipe/spipe/doc/00_llm_process/template/{feature,layer}_skill.md`. Commit the
wiki update in the same change as the work it describes.
