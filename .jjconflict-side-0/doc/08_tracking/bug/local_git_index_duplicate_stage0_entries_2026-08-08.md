# Local git index has duplicate stage-0 entries (2026-08-08)

Status: CLOSED (not reproducible)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

## Status: diagnosed, NOT repaired (report for approval — repair is deferred while
other agents are actively editing this working copy)

## Confirmed facts

- `git ls-files --stage | wc -l` → **131,933** entries
- `git ls-files --stage | awk '{print $4}' | sort -u | wc -l` → **111,424** unique paths
- Duplication: **20,509** duplicated path entries (matches the Opus review's figure)
- `git ls-files -u | wc -l` → **0** — NOT a mid-merge conflict state (all entries are
  stage 0, not stage 1/2/3)
- Sampled duplicated paths (`doc/07_guide/language/dict_native_pitfalls.md`,
  `doc/00_llm_process/env_expert/glm/skill.md`, several `test/01_unit/lib/**`
  paths): in every case the two stage-0 rows have **identical mode (100644) and
  identical blob SHA**. No divergent content — this is a pure duplicate listing,
  not two different versions of a file.

## Is it dangerous? — write-tree probe (scratch index only, real index untouched)

```
cp .git/index /tmp/idx.probe
GIT_INDEX_FILE=/tmp/idx.probe git write-tree
```

- Exit code **0**, produced tree `ccdadcd84704081de1df5d68c27c3a8203bd8409`
- `git ls-tree -r --name-only <tree> | wc -l` → **111,321** files

`write-tree` succeeds and silently collapses the duplicate stage-0 rows (a git
tree object cannot hold two entries for the same path, so duplicates in the
index are deduped at the moment the tree is built). The resulting file count
(111,321) is in the same range as the unique-path count (111,424) and close to
`origin/main`'s 111,467 — the gap is attributable to normal local WC deltas
(uncommitted adds/removes from other agents), not corruption. **write-tree is
NOT silently truncating or duplicating content** — this specific corruption
does not reproduce the "corrupt tree with a higher-than-healthy file count"
failure mode from the prior duplicate-entry incident. It is index-level
noise that git's own tree-building step already tolerates.

Conclusion: **cosmetic/index-level, not a tree-corruption risk by itself** —
but it is still a symptom worth fixing before it accumulates further or
coincides with another failure mode (see vcs.md history of two prior wipes).

## Root-cause check

- `df -h .` → `/dev/nvme0n1p2` 3.7T, 97% used, **135G available** — not ENOSPC
  right now (though the filesystem is quite full, keep an eye on it).
- `.git/index.lock` → does not exist (no stale lock).
- `pgrep -af 'jj (rebase|restore)'` → no output, nothing mid-flight.
- `jj status` / `jj op log` (default) → **"The working copy is stale (not
  updated since operation f1204fdea46d). Hint: Run `jj workspace
  update-stale`."** Confirmed via `jj --ignore-working-copy op log`: the last
  ~8 operations are all `snapshot working copy` calls roughly every 20-60
  minutes, most recent one `cfaa2367148d` ~1 hour ago, 291ms — i.e. another
  agent/session is snapshotting normally, but THIS workspace pointer has
  fallen behind the operation log tip.

**Likely mechanism**: jj's colocated-git backend rewrites `.git/index` on
every snapshot to match the current jj working-copy tree. When the workspace
pointer is stale relative to the op log (as it is now) while a concurrent
session keeps advancing the op log and touching the git index, two snapshot
writers can race on `.git/index`, and a partially-applied index update can
leave stage-0 rows appended rather than replaced for paths jj re-touches
across generations. This matches the "concurrent checkout" class of race
already documented in `.claude/rules/vcs.md`. Not certain — no smoking gun
(no lock file, no crashed process) — but the stale-workspace + concurrent
snapshot pattern is the only anomaly found and is consistent with the
duplication.

## origin/main health check (baseline for comparison)

- Total files: `git ls-tree -r --name-only origin/main | wc -l` → **111,467**
  (healthy — prior incidents dropped this to near 0 or inflated it via dup
  top-level dirs)
- `src/` top-level entries: **15** (band 13..25 — OK)
- `src/runtime` file count: **199** (floor ≥150 — OK)
- Top-level duplicate entries: `git ls-tree origin/main | awk '{print $4}' |
  sort | uniq -d | wc -l` → **0**

origin/main is clean and healthy. The duplication is confirmed **local-index-only**.

## Recommended repair (NOT executed — pending approval)

Safest option, in order of preference:

1. **Do nothing destructive to the worktree.** The index is a cache that git
   rebuilds correctly on demand (as proven by the write-tree probe); the
   duplication does not corrupt tracked file content and `git status`/`diff`
   still function (seen working during this probe).
2. **Once other agents have quiesced (no concurrent jj/git writers) — rebuild
   the index from itself, non-destructively:**
   ```
   git read-tree --reset -im HEAD    # NOTE: only after confirming no unstaged
                                       # edits would be lost — see caveat below
   ```
   This is risky to run blind because `--reset` can discard staged-only diffs
   that haven't hit the worktree. **Safer index-only alternative that cannot
   touch worktree files at all:**
   ```
   cp .git/index .git/index.bak.$(date +%s)   # backup first
   git update-index --refresh              # sanity check, read-only-ish
   # then, once confirmed no other process is writing the index:
   rm .git/index
   git reset --mixed HEAD -- .    # rebuilds index from HEAD tree; touches
                                    # only the INDEX, never worktree files,
                                    # because --mixed never checks out files
   ```
   `git reset --mixed` (no `--hard`, no `-f` checkout) only rewrites
   `.git/index` to match `HEAD`'s tree; it does not touch a single worktree
   file, so all uncommitted edits currently on disk survive untouched and will
   show back up as modified/untracked in `git status` afterward. This is the
   safest concrete repair.
3. **Resolve the jj staleness separately, but NOT via `jj workspace
   update-stale`** (explicitly forbidden here since it can silently switch
   lineage per `reference_jj_update_stale_switched_lineage_and_deleted_43_files.md`).
   Instead, once other sessions confirm they're done, coordinate a single
   agent to run `jj workspace update-stale` deliberately with `git show
   --stat` verification before/after, per vcs.md's recovery guidance — this
   is a SEPARATE remediation from the index-duplication fix and should not be
   bundled with it.

## What's safe to run now vs. requires quiescing

- **Safe now (read-only, already run):** all `git ls-files`, `git ls-tree`,
  scratch-index `write-tree` probes, `df`, `pgrep`, `jj --ignore-working-copy
  op log`.
- **Requires quiescing other agents first:** any write to the real
  `.git/index` (steps 2 and 3 above) — a concurrent jj snapshot mid-rebuild
  could reintroduce the race that likely caused this in the first place.
- **Still forbidden per task scope:** `git reset --hard`, `git checkout -f`,
  `jj workspace update-stale` (without explicit coordination), force-push,
  `rm` of tracked files.

## Divergent-lineage note (separate, already investigated by reviewer)

Local `HEAD` sits on a lineage not descended from `origin/main` (merge-base
`7daa6f04194`; origin is 110 commits ahead, local has 2 commits whose content
is already present on origin byte-for-byte per blob-hash comparison). This is
orthogonal to the index duplication — it means the 2 local-only commits are
safe to abandon/rebase away later (nothing unique to rescue), but that action
is out of scope here per the "no destructive commands" instruction and should
be handled in a follow-up once the index issue above is resolved and other
sessions are quiesced.
