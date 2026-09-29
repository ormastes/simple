# The silent rewind: a stale merge snapshot that deletes landed work and merges cleanly

A long-lived branch whose author re-synced by **snapshotting a whole tree**
rather than merging carries the state of `main` as it was when they snapshotted.
Every line that landed on `main` after that moment is, in the branch's tree,
simply absent. When the PR is merged, those lines are deleted.

**No tool reports a conflict for this.** `git merge-tree` is clean, GitHub says
"able to be merged", and the PR's own diff view — which many readers skim for
additions — shows the deletions only if you scroll to them.

## Why merge-tree is clean

A conflict requires both sides to have changed the same region since the merge
base. Here only one side did: the branch removed the lines, and `main` has not
touched them since the base. A one-side-only change auto-resolves, and "removed"
is a change like any other. Merge is doing exactly what it is defined to do; the
defect is upstream, in how the branch was synced.

This is the same failure class as the sync-commit clobbers described in
`.claude/rules/vcs.md` § "Sync must never clobber (anti-revert protocol)", but
arriving through a reviewed PR rather than a `chore(sync)` commit, which is why
the anti-revert protocol's step 3 does not catch it: nobody runs it on someone
else's PR.

## What it looked like, measured 2026-09-06

Four PRs reviewed in a single session each carried one of these, and all four
merged cleanly by every automated signal:

- `host_path_native` call sites went from 19 to 0 — a whole landed API
  migration erased. (For scale: `grep -rn host_path_native src/` returns 76
  lines at `origin/main` today.)
- 23 files that a repo-root purge had removed were restored.
- Two **blocking** gates were removed from `.github/workflows/repo-hygiene.yml`.
- A `uint64_t` -> `uint32_t` widening fix in a `baremetal_stubs.c` was reverted.

Note the shape: three of the four are *shared meta files* — CI workflow
definitions, gate manifests, root layout — which almost every branch touches and
almost no reviewer diffs. That is where this hides.

## Detection recipe

Run it **after update-branch**, when `HEAD` already contains `origin/main` (which
strict up-to-date enforces anyway — see
`doc/07_guide/infra/vcs/pr_landing_timing_race.md`). Then a two-dot diff means
"lines this branch removes from `main`":

```bash
git diff origin/main..HEAD -- <path> | grep -c '^-[^-]'
```

For a shared meta file the answer should be **0**. Any nonzero count needs a
human reading the deletions before merge.

Before update-branch, use the merge-base form instead, or the two-dot count will
also include everything `main` gained since you branched:

```bash
git diff origin/main...HEAD -- <path> | grep -c '^-[^-]'
```

`^-[^-]` is a heuristic (it excludes the `---` file header but counts a deleted
line that itself starts with `-`). Pair the count with
`git diff origin/main..HEAD --stat` and actually read the deletions — the count
tells you *whether* to look, not *what* happened.

## The path list worth checking on every PR

Any file that many branches touch and no one owns:

- `.github/workflows/**` — especially `repo-hygiene.yml`
- `config/check/must_check_gates.sdn` and `scripts/check/*_baseline.txt`
- root-level layout: `FILE.md` manifests, `.gitignore`
- any symbol whose call sites were recently migrated in bulk

## Relation to the automated guards

`scripts/check/check-runtime-api-regression-push.shs` is the closest existing
automated analogue of this recipe, scoped to `rt_*` symbol *definitions*. The
tree-structure guards in `.claude/rules/vcs.md` § Pre-push guards — conflict
entries, marker text, file counts, compilability — cannot see this at all: a
stale snapshot is structurally perfect. Until a general version of this exists, the check is
manual and belongs in PR review.
